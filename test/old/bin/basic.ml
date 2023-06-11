open Sexplib.Std

let compare_string = String.compare
let equal_string = String.equal

type term = Const of string | App of term * term | Var of string
[@@deriving sexp_of, compare, equal]

let rec subterm sub t = equal_term sub t || strict_subterm sub t

and strict_subterm sub t =
  match t with App (f, x) -> subterm sub f || subterm sub x | _ -> false
(*
  | Set of term list 
  | MultiSet of term list 
  | Map of (term * term) list
  | Linear of (int * term) list  (* float? Q? *)  (* Vector of (scalar * term) list *)
  | Lam of term
  | BVar of int

type lit = Q of Q | R of float | Int of int | Const of string | C of complex | Skolem of int
type term = Lit of lit
*)

(*
linmatch pat a =
  div   

setmatch pat t = 
 
multisetmatch pat t =
*)

(*
   let set_ ls = Set (List.sort_uniq ls)
   let multiset ls = MultiSet (List.sort ls)
*)

let rec sexp_of_term =
  let open Sexplib in
  function
  | Const a -> Sexp.Atom a
  | Var a -> Sexp.Atom a
  | App (f, x) -> (
      let x = sexp_of_term x in
      let f = sexp_of_term f in
      match f with
      | Sexp.List l -> Sexp.List (l @ [ x ])
      | _ -> Sexp.List [ f; x ])

let pp_term ppf x = Sexplib.Sexp.pp_hum ppf (sexp_of_term x)

let app (f : term) (args : term list) : term =
  List.fold_left (fun f x -> App (f, x)) f args

let rec term_of_sexp =
  let open Sexplib in
  function
  | Sexp.Atom a -> if String.contains a '?' then Var a else Const a
  | Sexp.List [] -> Const "nil"
  | Sexp.List [ x ] -> term_of_sexp x
  | Sexp.List (h :: xs) ->
      List.fold_left
        (fun acc x -> App (acc, term_of_sexp x))
        (term_of_sexp h) xs

module Term = struct
  type t = term

  let compare = compare_term
end

module StringMap = Map.Make (String)
module TermMap = Map.Make (Term)
module TermSet = Set.Make (Term)
(* Apply term * term  ?? *)

module Trie = struct
  (* https://www.lri.fr/~filliatr/ftp/ocaml/misc/trie.ml.html *)
  (* type token = App | Const of string  *)
  type token = string option
  type key = token list
  type 'a t = { value : 'a option; app : 'a t option; const : 'a t StringMap.t }

  let empty = { value = None; app = None; const = StringMap.empty }

  let rec find_opt key t =
    match key with
    | [] -> t.value
    | None :: k -> Option.bind t.app (find_opt k)
    | Some s :: k -> Option.bind (StringMap.find_opt s t.const) (find_opt k)

  let rec add key v t =
    match key with
    | [] -> { t with value = v }
    | None :: k ->
        let t' = Option.value ~default:empty t.app in
        { t with app = Some (add k v t') }
    | Some s :: k ->
        let t' = StringMap.find_opt s t.const |> Option.value ~default:empty in
        { t with const = StringMap.add s (add k v t') t.const }

  let map = ()
  let fold = ()
  let iter = ()
end

(*
type where =  Left of term | Right of term (* | SubTermRight of term | SubTermLeft of term *)
type egraph = where trie   


subterm_trie as analog of suffix trie
*)

let rec size = function
  | Const _ -> 1
  | App (f, x) -> size f + size x
  | Var _ -> failwith "size does not support Var"
(* List.fold_left (fun acc a -> acc + size a) (size a) args *)

let rec ground_kbo t1 t2 =
  let s1 = size t1 in
  (* obviously silly to be recomputing thi a bunch *)
  let s2 = size t2 in
  if Int.equal s1 s2 then
    match (t1, t2) with
    | Const x1, Const x2 ->
        String.compare x1 x2 (* could compare weights first *)
    | Const _, App (_, _) -> -1
    | App (_, _), Const _ -> 1
    | App (f1, args1), App (f2, args2) ->
        let cf = ground_kbo f1 f2 in
        if Int.equal cf 0 then ground_kbo args1 args2 else cf
    | Var _, _ | _, Var _ -> failwith "ground kbo does not support var"
  else Int.compare s1 s2

type egraph = term TermMap.t

let pp_egraph ppf (m : egraph) =
  TermMap.iter
    (fun k v -> Format.fprintf ppf "%a -> %a@\n" pp_term k pp_term v)
    m

let pp_termset ppf (m : TermSet.t) =
  TermSet.iter (fun k -> Format.fprintf ppf "%a@\n" pp_term k) m

let invert (e : egraph) : term list TermMap.t =
  TermMap.fold
    (fun k v acc ->
      TermMap.update v
        (fun ot -> match ot with Some x -> Some (k :: x) | None -> Some [ k ])
        acc)
    e TermMap.empty

(*
we are assuming in fully compressed form.
*)
let reduce e t =
  let rec worker t =
    match TermMap.find_opt t e with
    | Some t -> t
    | None -> (
        match t with
        | Const _ -> t
        | App (f, x) -> App (worker f, worker x)
        | Var _ -> failwith "reduce does not support var")
  in
  worker t

(* conversely, find does not recurse into the term but does not assume compressed form *)
let find_no_sub e t =
  let rec worker t =
    match TermMap.find_opt t e with None -> t | Some t -> worker t
  in
  worker t

(* recursing down is doing congruence closure. Doing a traversal like this is expensive. *)
let find e t =
  let rec worker t =
    match t with
    | Const _ -> find_no_sub e t
    | App (f, x) ->
        let t = App (find_no_sub e (worker f), find_no_sub e (worker x)) in
        find_no_sub e t
    | Var _ -> failwith "reduce does not support var"
  in
  worker t

type subst = (string * term) list

let pp_subst ppf subst =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.pp_print_char ppf ';')
    (fun ppf (v, t) ->
      Format.fprintf ppf "(%a,%a)" Format.pp_print_string v pp_term t)
    ppf subst

let ematch e pat t : subst list =
  let eclass = invert e in
  (* lift find e t to outer? *)
  let rec worker pat t subst =
    match (pat, t) with
    | Const x, Const y ->
        if String.equal x y || equal_term (find e pat) (find e t) then [ subst ]
        else []
    | App (f, x), App (f2, x2) -> (
        List.concat_map (fun subst -> worker x x2 subst) (worker f f2 subst)
        @
        match TermMap.find_opt t eclass with
        | None -> []
        | Some enodes ->
            List.concat_map
              (fun t -> worker pat t subst)
              enodes (* The kbo order mght protect us here *))
    | _, Var _ -> failwith "ematch does not support Var in term"
    | Var x, _ -> (
        match List.assoc_opt x subst with
        | None -> [ (x, t) :: subst ]
        | Some t' -> if equal_term t t' then [ subst ] else [])
    | App (_, _), Const _ | Const _, App (_, _) -> []
  in
  worker pat t []

let ematch_all e pat =
  let terms =
    TermMap.fold
      (fun t1 t2 s -> TermSet.add t1 (TermSet.add t2 s))
      e TermSet.empty
  in
  (* let eclasses = invert e in *)
  let terms = TermSet.to_seq terms in
  Seq.map (ematch e pat) terms

let rec add_subterms t tset =
  let tset = TermSet.add t tset in
  add_subterms_strict t tset

and add_subterms_strict t tset =
  match t with App (f, x) -> add_subterms x (add_subterms f tset) | _ -> tset

let eclasses e =
  TermMap.fold
    (fun lhs rhs tset ->
      let tset = add_subterms rhs tset in
      add_subterms_strict lhs tset)
    e TermSet.empty

let ( let* ) x f = List.concat_map f x

(*
subst list TermMap.t   
Or 
If we use a trie of the bound values, we can do gj kind of?

*)
let bottom_up (e : egraph) pat =
  let eclasses = eclasses e in
  let elist = TermSet.to_seq eclasses |> List.of_seq in
  let rec worker subst pat =
    match pat with
    | Const s ->
        let t = reduce e pat in
        (* reduce vs find_no_sub vs find? *)
        [ (t, subst) ]
    | Var v -> (
        match List.assoc_opt v subst with
        | None -> List.map (fun eid -> (eid, (v, eid) :: subst)) elist
        | Some eid -> [ (eid, subst) ])
    | App (f, x) ->
        let* f, subst = worker subst f in
        let* x, subst = worker subst x in
        let eid = reduce e (App (f, x)) in
        (* I should compress things here *)
        if TermSet.mem eid eclasses then [ (eid, subst) ] else []
  in
  (* Hmm maybe this is now redundant *)
  (* List.filter (fun (t, _subst) -> TermSet.mem t eclasses) (worker [] pat) *)
  worker [] pat

let instan subst pat =
  let rec worker pat =
    match pat with
    | Const _ -> pat
    | Var x -> Option.value ~default:pat (List.assoc_opt x subst)
    | App (f, x) -> App (worker f, worker x)
  in
  worker pat

let union e x y =
  let x = find e x in
  let y = find e y in
  let ord = ground_kbo x y in
  match ord with
  | 0 -> e
  | 1 -> TermMap.add x y e
  | -1 -> TermMap.add y x e
  | _ -> failwith "impossible case"

let apply_rule e lhs rhs =
  let substs = ematch_all e lhs in
  Seq.fold_left
    (fun e substs ->
      List.fold_left
        (fun e subst -> union e (instan subst lhs) (instan subst rhs))
        e substs)
    e substs

(*
  let lhs_strict_subterms e =
    TermMap.fold
      (fun lhs _rhs tset -> add_subterms_strict lhs tset)
      e TermSet.empty
*)
(*
A mapping from subterms to lhs/rhs term sounds useful. a bool for lhs/rhs?

*)
let rec mem_subterm lhs tset =
  TermMap.mem lhs tset || mem_strict_subterm lhs tset

and mem_strict_subterm t tset =
  match t with
  | App (f, x) -> mem_subterm f tset || mem_subterm x tset
  | _ -> false

(* Would Tries help us do these traversals faster? *)
let canon e =
  let rec worker e =
    (* l-simplify *)
    let e' =
      TermMap.fold
        (fun lhs rhs e ->
          if mem_strict_subterm lhs e then
            let e = TermMap.remove lhs e in
            union e lhs rhs
          else e)
        e e
    in
    (* r-simplify *)
    let e' = TermMap.map (reduce e') e' in
    (* could fold this in above to avoid second traversal *)
    if TermMap.equal equal_term e e' then e else worker e'
  in
  worker e

let true_ = Const "true"

type st = { egraph : egraph; rules : (term * term) list }

let pp_st ppf st =
  Format.fprintf ppf "{egraph = %a; @\n rules = %a}@\n" pp_egraph st.egraph
    (Format.pp_print_list (fun ppf (lhs, rhs) ->
         Format.printf "%a -> %a@\n" pp_term lhs pp_term rhs))
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
  | _ -> failwith "unspported action"

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

(*

Thoughts:
Trie specialized to Term. 
Hash Consing
String interning
metadata like size etc. Analyses


incremental ematching via narrowing. A shadow egraph?
term TermMap.t is a total accident. Other orderings





*)
