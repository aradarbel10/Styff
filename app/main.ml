open Styff.Exec

let () =
  try
    print_newline ();
    ignore (compile_prog `file debug_opts "examples/adt.stf");
  with
  | CompileFailure msg -> print_endline ("compilation failure: " ^ msg);