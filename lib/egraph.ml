open Term

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
        (* Boring case that occurs in ordinary matching *)
        List.concat_map (fun subst -> worker x x2 subst) (worker f f2 subst)
        @
        (* Interesting case where we match via a simplification rule *)
        match TermMap.find_opt t eclass with
        | None -> []
        | Some enodes -> List.concat_map (fun t -> worker pat t subst) enodes
        (* The kbo order mght protect us here. Naively this looks like an infinite loop *)
        )
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
    | Const _s ->
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
