open Js_of_ocaml
open Lambda_egglog

let _ =
  Js.export "Egglog"
    (object%js
       method run_egglog s =
         let t = Sexplib.Sexp.of_string_many_conv_exn s Action.t_of_sexp in
         Action.run_program t
    end)

let () = print_endline "egglog loaded"
