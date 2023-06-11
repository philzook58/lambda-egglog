open Logtk
open Containers

(*
https://github.com/sneeuwballen/zipperposition/blob/master/src/core/Congruence.ml
Ok, a question. Why am I not using this?

Is doing path compression during find even all that great. Seems kind of silly.
Just batch it up. I guess if you think you won't call find on most things? Laziness is best when you aren't going to 
  touch stuff.

Using a ref means ematching becomes nearly impossible.

*)

let prec = Precedence.default []
let ordering = Ordering.kbo prec

type t = Term.t Term.Map.t

(*
Indexing strategies:
- first symbol
- depth and size indexing number of symbols. Basically the Fingerprint indexes, so I should look at those.
*)
let pp ppf = Term.Map.pp Term.TPTP.pp ppf
let empty = Term.Map.empty
(* proof :
   mayyyyybe eqs : (Term.t * Term.t) Set.t
*)

let rec find (e : t) (x : Term.t) =
  let x' = Term.replace_m x e in
  if Term.equal x x' then x else find e x'
(* Term.Map.get_or x e ~default:x *)

let union (e : t) (x : Term.t) (y : Term.t) : t =
  assert (Term.is_ground x);
  assert (Term.is_ground y);
  Format.printf "union (%a) (%a)@." Term.TPTP.pp x Term.TPTP.pp y;
  let x = find e x in
  let y = find e y in

  Format.printf "find (%a) (%a)@." Term.TPTP.pp x Term.TPTP.pp y;
  if Term.equal x y then e
  else
    let open Comparison in
    match Ordering.compare ordering x y with
    (* hmm might_flip. Is that a useful fast path? *)
    | Eq ->
        failwith
          (Format.sprintf "Terms %a %a are equal under kbo?" Term.TPTP.pp x
             Term.TPTP.pp y)
        (* Format.printf "Eq (%a) (%a)@." Term.TPTP.pp x Term.TPTP.pp y;
           e (* hmm should we perhaps insert self identity stuff in? *) *)
    | Gt ->
        Format.printf "Gt add (%a) (%a)@." Term.pp x Term.pp y;
        Term.Map.add x y e
    | Lt ->
        Format.printf "Lt add (%a) (%a)@." Term.pp x Term.pp y;
        Term.Map.add y x e
    | Incomparable ->
        (* order should be complete over ground terms. *)
        failwith
          (Format.sprintf "Unexpected incomparable terms in union: %a %a"
             Term.pp x Term.pp y)

let assert_fact (e : t) (x : Term.t) : t = union e x Term.true_

(* We could have a better index on here rather than traversing the term.
    Although, honeslty, maybe not too bad?
   I'm not sure traversing the term liek this is ok for lambdas.
*)
let has_subterm_strict (e : t) (t : Term.t) : bool =
  Iter.exists
    (fun (t, p) -> Term.Map.mem t e && not (Position.equal p Position.Stop))
    (Term.all_positions t)

let canonize (e : t) : t =
  (* r-simplify *)
  (* let e = Term.Map.map (fun t -> find e t) e in *)
  let rec canon_step e =
    let e' =
      Term.Map.fold
        (fun lhs rhs e ->
          if has_subterm_strict e lhs then
            let e = Term.Map.remove lhs e in
            (* l-simplify *)
            union e lhs rhs
          else Term.Map.add lhs (find e rhs) e)
          (* r-simplify. Note this is also critica pair finding deduce.
             The only critical pairs that can occur are (strict) subterm relationships. *)
        e e
    in
    if Term.Map.equal Term.equal e e' then e else canon_step e'
  in
  canon_step e

(*
   
*)

(* what about
   let e = Term.Map.remove lhs e in
   union e lhs rhs

   Is this ok to parallelize out of curiosity?
         Format.printf "attempting %a <---> %a\n" Term.TPTP.pp t Term.TPTP.pp    pattern;
*)

let ematch (e : t) (pattern : Term.t) : Subst.t Iter.t =
  Iter.filter_map
    (fun t ->
      Format.printf "t: %a   pat: %a@." Term.TPTP.pp t Term.TPTP.pp pattern;
      try
        let match_ = Unif.FO.matching_same_scope ~pattern ~scope:0 t in
        Format.printf "match : %a@." Subst.pp match_;
        Some match_
      with Unif.Fail -> None)
    (Iter.flat_map
       (fun t -> Iter.map (fun (t, _pos) -> t) (Term.all_positions t))
       (Iter.append (Term.Map.keys e) (Term.Map.values e)))

(*
   
match Term.view pattern with 
| App (sy, args) -> 
| Var i -> 
*)

(*
Egraph implicitly contains an inductive unverse of terms.
Start with set of all rhs and apply rules expansively right to left.
This may or may not be terminating / finite.

Can this be interpreted coinductivtly?


This is not right. Need to check _subterms_ also. k now it's right (or at least as far as I'm aware.)
*)
let mem (e : t) (t : Term.t) : bool =
  let t' = find e t in
  (* reduce*)
  Iter.exists
    (fun t -> Term.subterm ~sub:t' t)
    (Iter.append (Term.Map.values e) (Term.Map.keys e))

(*
Subproblems:
Consider ground ematching rules
foo (foo (foo (foo x))) -> x   

Need to fix term parser


ematching is an application of deduce. (sort of). 
However i so choose to deduce a ground equation is chill.

ideas:
1. critical pairs with lhs (and rhs?). Only accept if reduced lhs is already "in" egraph
2. bottom up


We don't _have_ to follow traditional ematching if it's inconvenient. It's all heuristic anyway.
There is a very natural definition of mem and basically ematching should be inverting the mode of that relatinship though.

Matching at the top of left or rhs is too naive although valid. Maybe should do it anyway because it's so easy
 (and possibly more profitable in terms of shrinking egraph)

consider:
egraph : foo a = a
rule: foo (foo (foo (foo x))) -> bar x 

Guess and check 1: bind every variable to a lhs or rhs. Check `mem`
Guess and check 2 (strictly more powerful): bind every variable to all posible critical overlaps
It's interesting that we ground all variables at once.

British museum: generate the term expansion using right to left rules and pattern match on it
Brish-n - expand out N iterations of british museum.
British-Iterative-deepending - expand out N for increasing N.
I don't thnk british museum will generate anything critical pair won't catch.


Question: termination properties of different strategies.

*)
