open Lambda_egglog
open Term
open Egraph
open Sexplib.Std

type st = { egraph : egraph; rules : (term * term) list }

let pp_st ppf st =
  Format.fprintf ppf "{egraph = %a; @\n rules = %a}@\n" pp_egraph st.egraph
    (Format.pp_print_list (fun ppf (lhs, rhs) ->
         Format.fprintf ppf "%a -> %a@\n" pp_term lhs pp_term rhs))
    st.rules

let empty_state = { egraph = TermMap.empty; rules = [] }

type action =
  | Rewrite of term * term
  | Assert of term
  | Extract of term
  | Union of term * term
  | Run of int
  | Print
  | Match of term
  | Clear
[@@deriving sexp]

let pp_action ppf a = Sexplib.Sexp.pp_hum ppf (sexp_of_action a)
let info = Format.printf

let run_action st = function
  | Assert t -> { st with egraph = TermMap.add t true_ st.egraph }
  | Rewrite (lhs, rhs) -> { st with rules = (lhs, rhs) :: st.rules }
  | Union (lhs, rhs) -> { st with egraph = union st.egraph lhs rhs }
  | Extract t ->
      info "%a" pp_term (reduce st.egraph t);
      st
  | Run _n ->
      let e = canon st.egraph in
      info "%a@\n" pp_egraph e;
      let e =
        List.fold_left (fun e (lhs, rhs) -> apply_rule e lhs rhs) e st.rules
      in
      { st with egraph = e }
  | Print ->
      Format.printf "%a@\n" pp_st st;
      st
  | Match p ->
      let matches = bottom_up st.egraph p in
      List.iter
        (fun (t, subst) -> Format.printf "%a: %a@\n" pp_term t pp_subst subst)
        matches;
      st
  | Clear -> empty_state

let process_file filename =
  (* let t_of_sexp s = s in *)
  let t = Sexplib.Sexp.load_sexps_conv_exn filename action_of_sexp in
  let egraph = ref empty_state in
  List.iter
    (fun action ->
      Format.printf "%a\n" pp_action action;
      egraph := run_action !egraph action)
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