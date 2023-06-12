open Sexplib.Std

let compare_string = String.compare
let equal_string = String.equal

type term = Const of string | App of term * term | Var of string
[@@deriving sexp_of, compare, equal]

type t = term

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

module TermMap = Map.Make (Term)
module TermSet = Set.Make (Term)
(* Apply term * term  ?? *)

module Trie = struct
  (* https://www.lri.fr/~filliatr/ftp/ocaml/misc/trie.ml.html *)
  (* type token = App | Const of string  *)
  type token = string option
  type key = token list

  module StringMap = Map.Make (String)

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

let true_ = Const "true"

(* https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf *)

module HTerm = struct
  type hterm = term_node Hashcons.hash_consed
  (* Might want to copy over the hashcons lib so we can tuck extra metadata in the nodes. *)
  (* { tag : int; node : term_node; hkey : int } *)

  and term_node = Var of string | Const of string | App of hterm * hterm

  let equal_term (x : hterm) (y : hterm) = Int.equal x.tag y.tag
  let compare_term (x : hterm) (y : hterm) = Int.compare x.tag y.tag

  module T = struct
    type t = term_node

    let equal x y =
      match (x, y) with
      | Var s, Var s' | Const s, Const s' -> String.equal s s'
      | App (f, x), App (f', x') -> equal_term f f' && equal_term x x'
      | _, _ -> false

    let hash = function
      | Var s -> Hashtbl.hash s
      | Const s -> Hashtbl.hash s + 1
      | App (f, x) -> (19 * ((19 * f.hkey) + x.hkey)) + 2
  end

  module Hterm = Hashcons.Make (T)

  let ht = Hterm.create 251
  let var n = Hterm.hashcons ht (Var n)
  let const u = Hterm.hashcons ht (Const u)
  let app u v = Hterm.hashcons ht (App (u, v))

  module Set = Hashcons.Hset
  module Map = Hashcons.Hmap

  let rec of_term : term -> hterm = function
    | Const s -> const s
    | Var s -> var s
    | App (f, x) -> app (of_term f) (of_term x)
end

(* Move term down here so we can put hterm inside of term? *)

(* Generic Join translated to trees *)
(*
   module Subst = struct
     type 'a t =
       { pat : term ; value TermMap.t  }
   end
*)
(* HashConsed hash joins *)
