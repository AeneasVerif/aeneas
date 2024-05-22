let concat_path = List.fold_left Filename.concat ""

let () =
  match Array.to_list Sys.argv with
  (* Ad-hoc argument passing for now. *)
  | _exe_path :: aeneas_path :: tests_dir :: test_name :: subdir :: backend
    :: options ->
      let input_file = concat_path [ tests_dir; "llbc"; test_name ] ^ ".llbc" in
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
