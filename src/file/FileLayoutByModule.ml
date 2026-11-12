open FileLayout

let name = "split by module"

(** The files of a component (see {!FilePlan} for what components and layers
    are). [component_of_scc] gives the component of each SCC of the file graph.
*)
let component_files (fg : FileGraph.t)
    (component_of_scc : FilePlan.component SCC.SccId.Map.t)
    (m : FilePlan.component) : file list =
  if m.is_dropped then []
  else
    let filter =
      {
        (all_decls ()) with
        (* Not supported with [-split-files] (CLI rejects this combination). *)
        extract_decreases_clauses = false;
        extract_template_decreases_clauses = false;
      }
    in
    (* The first layer imports the components this one depends on, except the
       dropped ones, which have no file. *)
    let deps =
      Option.value
        (SCC.SccId.Map.find_opt m.scc_id fg.sccs.scc_deps)
        ~default:SCC.SccId.Set.empty
    in
    let dep_imports =
      List.filter_map
        (fun dep_id ->
          let dep = SCC.SccId.Map.find dep_id component_of_scc in
          if dep.is_dropped then None else Some dep.import_name)
        (SCC.SccId.Set.elements deps)
    in
    (* A component with several Rust modules lists them in its header. *)
    let sources_msg =
      if List.length m.modules > 1 then
        ": merged from "
        ^ String.concat ", "
            (List.map FileGraph.module_path_to_string m.modules)
      else ""
    in
    (* Each subsequent layer just imports the previous one. *)
    let _, layers =
      List.fold_left_map
        (fun includes (layer : FilePlan.component_layer) ->
          let header =
            if layer.is_opaque_layer then
              (if m.is_external then ": external declarations"
               else ": opaque declarations")
              ^ ".\n\
                 -- This is a template file: rename it to drop the \
                 \"_Template\" suffix and fill the holes."
            else sources_msg
          in
          ( [ layer.import_name ],
            {
              path = layer.filename;
              module_name = layer.import_name;
              imports = [];
              includes;
              contents =
                Definitions
                  {
                    header;
                    groups = Some layer.groups;
                    filter = { filter with interface = layer.is_opaque_layer };
                    (* Local modules are in the crate namespace. An external
                       module can't open it. *)
                    in_namespace = not m.is_external;
                    open_namespace = false;
                    noncomputable = layer.noncomputable;
                  };
              protect_user_file = false;
            } ))
        dep_imports m.layers
    in
    (* The aggregator imports the layers, so that other files can import the
       module by its plain name. It imports the opaque layers by the name of
       their filled copy, so it only builds once the user has filled them in. *)
    let aggregator =
      match m.aggregator with
      | None -> []
      | Some path ->
          [
            {
              path;
              module_name = m.import_name;
              imports =
                List.map
                  (fun (l : FilePlan.component_layer) -> l.import_name)
                  m.layers;
              includes = [];
              contents =
                ImportsOnly
                  {
                    header =
                      Some (": imports the layers of this module" ^ sources_msg);
                  };
              protect_user_file = false;
            };
          ]
    in
    layers @ aggregator

let plan (env : env) : plan =
  let { crate; crate_name; dest_dir; subdir; full_dest_dir; import_prefix; _ } =
    env
  in
  let fg = Lazy.force env.file_graph in
  let components =
    FilePlan.place_by_file fg ~crate ~import_prefix
      ~module_root_dir:
        (FilePlan.module_root_dir ~subdir ~full_dest_dir ~crate_name)
      ~all_computable:!Config.all_computable
  in
  let component_of_scc =
    List.fold_left
      (fun acc (m : FilePlan.component) -> SCC.SccId.Map.add m.scc_id m acc)
      SCC.SccId.Map.empty components
  in
  (* The entry point (see {!FilePlan.entry_point_file}), so that [import Crate]
     imports the whole crate. *)
  let entry_point = FilePlan.entry_point_file ~subdir ~dest_dir ~crate_name in
  let entry_point_file =
    match entry_point with
    | None -> []
    | Some path ->
        [
          {
            path;
            module_name = crate_name;
            imports =
              List.filter_map
                (fun (m : FilePlan.component) ->
                  (* This also skips the dropped components, which are
                     external. *)
                  if m.is_external then None else Some m.import_name)
                components;
            includes = [];
            contents =
              ImportsOnly
                {
                  header =
                    Some
                      ": the library entry point: importing this module brings \
                       the whole crate into scope.";
                };
            (* Don't overwrite a file we didn't generate (e.g. one the user
               wrote). *)
            protect_user_file = true;
          };
        ]
  in
  {
    files =
      List.concat_map (component_files fg component_of_scc) components
      @ entry_point_file;
    report =
      Some
        (lazy (FilePlan.placement_to_string ~dest_dir ~entry_point components));
  }
