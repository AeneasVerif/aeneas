open FileLayout

let name = "single file"

let plan (env : env) : layout =
  let has_opaque_types, has_opaque_funs = has_opaque_decls env in
  let file =
    {
      path = Filename.concat env.full_dest_dir env.crate_name ^ file_ext ();
      module_name = env.crate_name;
      imports = [];
      includes = [];
      contents =
        Definitions
          {
            header = "";
            groups = None;
            filter = all_decls ();
            in_namespace = true;
            open_namespace = false;
            noncomputable =
              noncomputable_if_opaque (has_opaque_types || has_opaque_funs);
          };
      protect_user_file = false;
    }
  in
  { files = [ file ] }
