open Styff.Exec

let () =
  print_newline ();
  ignore (compile_prog_file {elab_diagnostics = true; dump_output = true} "examples/builtins.stf");