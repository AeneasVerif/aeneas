let concat_path = List.fold_left Filename.concat ""

let () =
  match Array.to_list Sys.argv with
  (* Ad-hoc argument passing for now. *)
  | _exe_path :: aeneas_path :: tests_dir :: test_name :: backend :: options ->
      (* Reproduces the file layout that was set by the Makefile. FIXME: cleanup *)
      let subdir =
        match (backend, test_name) with
        | "lean", "demo" -> "Demo"
        | "lean", _ -> "."
        | _, ("arrays" | "demo" | "hashmap" | "traits") -> test_name
        | _, "betree_main" -> "betree"
        | _, "betree_main-special" -> "betree_back_stateful"
        | _, "hashmap_main" -> "hashmap_on_disk"
        | "hol4", _ -> "misc-" ^ test_name
        | ( _,
            ( "bitwise" | "constants" | "external" | "loops"
            | "no_nested_borrows" | "paper" | "polonius_list" ) ) ->
            "misc"
        | _ -> test_name
      in

      let test_file_name =
        match test_name with
        | "betree_main-special" -> "betree_main"
        | _ -> test_name
      in
      let input_file =
        concat_path [ tests_dir; "llbc"; test_file_name ] ^ ".llbc"
      in
      let dest_dir = concat_path [ "tests"; backend; subdir ] in
      let args =
        [| aeneas_path; input_file; "-dest"; dest_dir; "-backend"; backend |]
      in
      let args = Array.append args (Array.of_list options) in

      (* Debug arguments *)
      print_string "[test_runner] Running: ";
      Array.iter
        (fun x ->
          print_string x;
          print_string " ")
        args;
      print_endline "";

      (* Run Aeneas *)
      let pid =
        Unix.create_process aeneas_path args Unix.stdin Unix.stdout Unix.stderr
      in
      let _ = Unix.waitpid [] pid in
      ()
  | _ -> ()
