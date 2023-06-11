open Lambda_egglog

let process_file filename =
  (* let t_of_sexp s = s in *)
  let t = Sexplib.Sexp.load_sexps_conv_exn filename Action.t_of_sexp in
  let egraph = ref Action.empty in
  List.iter
    (fun action ->
      Format.printf "%a\n" Action.pp action;
      egraph := Action.apply_action !egraph action)
    t;
  ()

let main () =
  let input_files = ref [] in
  (* let output_file = ref "" in *)
  let anon_fun filename = input_files := filename :: !input_files in
  let speclist = [] in
  let desc =
    "lambda-egglog - An egglog with support for lambdas and hypotheticals"
  in
  let () = Arg.parse speclist anon_fun desc in
  Format.printf "Loadng file: %s\n" (List.hd !input_files);
  process_file (List.hd !input_files);
  ()

let () = main ()
