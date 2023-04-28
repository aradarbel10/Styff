open Styff.Exec

open Js_of_ocaml
module Events = Js_of_ocaml_lwt.Lwt_js_events

let get_editor_contents () : Js.js_string Js.t = Js.Unsafe.js_expr "getEditorContents()"

let output_error : Js.js_string Js.t -> unit = Js.Unsafe.js_expr "outputError"
let output_clear : unit -> unit = Js.Unsafe.js_expr "outputClear"
let output_print : Js.js_string Js.t -> unit = Js.Unsafe.js_expr "outputPrint"

let onload _ =
  let button = Dom_html.getElementById "button" in
  button##.onclick := Dom_html.handler (fun _ ->
    output_clear ();
    let str = Js.to_string (get_editor_contents ()) in
    let js =
      try compile_prog `str {elab_diagnostics = false; dump_output = true; dump_visibles = false} str
      with | CompileFailure msg -> output_error (Js.string msg); ""
    in
    output_print (Js.string "compilation finished\n");
    ignore (Js.Unsafe.eval_string js);
    Js._false);

  Js._false

let () =
  Dom_html.window##.onload := Dom_html.handler onload;
