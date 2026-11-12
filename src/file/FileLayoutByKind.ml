open FileLayout

let name = "split by kind"

let plan (env : env) : layout =
  let { crate_name; full_dest_dir; import_prefix; _ } = env in
  let backend = Config.backend () in
  let ext = file_ext () in
  (* If the backend is Lean the module names depend on the path, so we generate
     names of the shape [Types.lean], [Funs.lean], etc. because those files
     should be placed in the proper sub-folder.

     Otherwise, we prepend the crate name to generate, e.g., [Foo_Types.fst],
     [Foo_Funs.fst], etc. *)
  let path_prefix =
    if backend = Lean then full_dest_dir ^ "/"
    else Filename.concat full_dest_dir crate_name ^ module_delimiter ()
  in

  (* Check if there are opaque types and functions (we need this to know whether
     we need to generate interface files, etc.) *)
  let has_opaque_types, has_opaque_funs = has_opaque_decls env in
  let needs_clauses_module =
    !Config.extract_decreases_clauses
    && not
         (PureUtils.FunLoopIdSet.is_empty
            (TranslateCore.translated_crate_rec_functions env.translated))
  in

  let base_filter =
    {
      no_decls with
      extract_decreases_clauses = !Config.extract_decreases_clauses;
      extract_transparent = true;
    }
  in
  let definitions_file ~(path : string) ~(module_name : string)
      ~(header : string) ?(imports : string list = [])
      ?(includes : string list = []) ?(open_namespace = false)
      ?(noncomputable = false) ~(in_namespace : bool) (filter : decl_filter) :
      file =
    {
      path;
      module_name;
      imports;
      includes;
      contents =
        Definitions
          {
            header;
            groups = None;
            filter;
            in_namespace;
            open_namespace;
            noncomputable;
          };
      protect_user_file = false;
    }
  in

  (* The file for the opaque declarations of the module [stem] (e.g.
     [TypesExternal]), with the name of the module the other files import.

     For F*, we generate an .fsti, and let the user write the .fst. For the
     other backends, we generate a template file as a model for the file the
     user has to provide: the module which is imported is the one the user
     writes. *)
  let external_file ~(stem : string) ~(kind : string) ~(rename_ext : string)
      ?(includes : string list = []) ~(open_namespace : bool)
      (filter : decl_filter) : file * string =
    let module_suffix, header =
      match backend with
      | FStar -> (stem, ": external " ^ kind ^ " declarations")
      | HOL4 | Coq | Lean ->
          ( stem ^ "_Template",
            ": external " ^ kind
            ^ "s.\n-- This is a template file: rename it to \"" ^ stem
            ^ rename_ext ^ "\" and fill the holes." )
    in
    ( definitions_file
        ~path:(path_prefix ^ module_suffix ^ interface_ext ())
        ~module_name:(import_prefix ^ module_suffix)
        ~header ~includes ~in_namespace:false ~open_namespace filter,
      import_prefix ^ stem )
  in

  (*
   * The types
   *)
  (* If there are opaque types, we extract them in an interface *)
  let opaque_types_file, opaque_types_module =
    if has_opaque_types then
      let file, imported =
        external_file ~stem:"TypesExternal" ~kind:"type" ~rename_ext:ext
          ~open_namespace:false
          {
            base_filter with
            extract_opaque = true;
            extract_transparent = false;
            extract_types = true;
            extract_trait_decls = true;
            interface = true;
          }
      in
      ([ file ], [ imported ])
    else ([], [])
  in

  (* The non opaque types *)
  let types_module = import_prefix ^ "Types" in
  let types_file =
    definitions_file
      ~path:(path_prefix ^ "Types" ^ ext)
      ~module_name:types_module ~header:": type definitions"
      ~includes:opaque_types_module ~in_namespace:true
      {
        base_filter with
        extract_types = true;
        extract_trait_decls = true;
        extract_opaque = false;
        interface = has_opaque_types;
      }
  in

  (* The template clauses *)
  let template_clauses_file =
    if needs_clauses_module && !Config.extract_template_decreases_clauses then
      [
        definitions_file
          ~path:(path_prefix ^ "Clauses" ^ file_delimiter () ^ "Template" ^ ext)
          ~module_name:
            (import_prefix ^ "Clauses" ^ module_delimiter () ^ "Template")
          ~header:": templates for the decreases clauses"
          ~imports:[ types_module ] ~in_namespace:true
          { base_filter with extract_template_decreases_clauses = true };
      ]
    else []
  in

  (*
   * The functions
   *)
  (* The opaque fun declarations, if needed *)
  let opaque_funs_file, opaque_funs_module =
    if has_opaque_funs then
      let file, imported =
        external_file ~stem:"FunsExternal" ~kind:"function" ~rename_ext:".lean"
          ~includes:[ types_module ] ~open_namespace:true
          {
            base_filter with
            extract_fun_decls = true;
            extract_trait_impls = true;
            extract_globals = true;
            extract_transparent = false;
            extract_opaque = true;
            interface = true;
          }
      in
      ([ file ], [ imported ])
    else ([], [])
  in

  (* The module the user writes for the decreases clauses *)
  let clauses_module =
    if needs_clauses_module then
      let clauses_submodule =
        if backend = Lean then "Clauses" ^ module_delimiter () else ""
      in
      [ import_prefix ^ clauses_submodule ^ "Clauses" ]
    else []
  in
  let funs_file =
    definitions_file
      ~path:(path_prefix ^ "Funs" ^ ext)
      ~module_name:(import_prefix ^ "Funs") ~header:": function definitions"
      ~includes:([ types_module ] @ opaque_funs_module @ clauses_module)
      ~in_namespace:true
      ~noncomputable:
        (noncomputable_if_opaque (has_opaque_types || has_opaque_funs))
      {
        base_filter with
        extract_fun_decls = true;
        extract_trait_impls = true;
        extract_globals = true;
      }
  in

  (* This layout has no entry point by default: [-gen-lib-entry] opts into
     generating a minimal [Crate.lean]. *)
  let entry_point =
    if backend = Lean && !Config.generate_lib_entry_point then
      [
        {
          path = Filename.concat env.dest_dir (crate_name ^ ".lean");
          module_name = crate_name;
          imports = [ crate_name ^ ".Funs" ];
          includes = [];
          contents = ImportsOnly { header = None };
          protect_user_file = false;
        };
      ]
    else []
  in

  {
    files =
      opaque_types_file @ [ types_file ] @ template_clauses_file
      @ opaque_funs_file @ [ funs_file ] @ entry_point;
  }
