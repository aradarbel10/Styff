open Styff.Exec

let () =
  try
    print_newline ();
    ignore (compile_prog `file {elab_diagnostics = true; dump_output = true} "examples/sections/section-shadowing.stf");
  with
  | CompileFailure msg -> print_endline ("compilation failure: " ^ msg);