(* open Sexplib *)
module Sexp = Sexplib.Sexp
open Sexplib.Std
module Term = Logtk.Term
module Type = Logtk.Type
module ID = Logtk.ID
open Containers

type sexp_term = Sexplib.Sexp.t [@@deriving sexp]

type t =
  | Rule of sexp_term list * sexp_term list
  | Assert of sexp_term
  | Extract of sexp_term
  | Union of sexp_term * sexp_term
  | Run of int
  | Function of string * string list * string
  | Relation of string * string list
  | Rewrite of sexp_term * sexp_term (* string *)
  | Sort of string
  | Print
  | Clear
  | Parse of string
[@@deriving sexp]

let pp ppf x = Sexp.pp_hum ppf (sexp_of_t x)

(*
let parse_action a =
  match a with
  | Sexp.Atom a -> failwith "unexpected atom"
  | Sexp.List [] -> failwith "unexpected empty sexp"
  | Sexp.List l -> 
    match l with
    | [Sexp.Atom "rule"; body; head] -> failwith "todo rule"
    | Sexp.Atom "rule" :: xs -> failwith "rule needs body and head"
    | Sexp.Atom "assert" :: term -> failwith "todo assert"
    *)

module StrMap = CCMap.Make (String)
module StrSet = CCSet.Make (String)
module StrTbl = CCHashtbl.Make (String)

(*
There is a question if I should use an egraph oriented version or just go full superposition.
Do I keep rules well separated from the egraph.
*)

type state = {
  egraph : Egraph.t;
  ids : ID.t StrTbl.t;
  (* consider using Logtk.Signature *)
  types : Type.t ID.Map.t;
  rewrites : (Term.t * Term.t) list;
      (* rules ;*)
      (* types : Term.t String.Map.t ;*)
}

let pp_state ppf s =
  Format.fprintf ppf "{egraph = %a;\ntypes = %a\n;rewrites = %a}"
    (Term.Map.pp Term.TPTP.pp Term.TPTP.pp)
    s.egraph (ID.Map.pp ID.pp Type.pp) s.types
    (List.pp (fun ppf (lhs, rhs) ->
         Format.fprintf ppf "%a --> %a" Term.TPTP.pp lhs Term.TPTP.pp rhs))
    s.rewrites

let empty =
  {
    egraph = Egraph.empty;
    ids = StrTbl.create 64;
    types = ID.Map.empty;
    rewrites = [];
  }

let id_of_string (s : string) st : ID.t =
  match StrTbl.get st.ids s with
  | None ->
      let id = ID.make s in
      StrTbl.add st.ids s id;
      Logtk.Precedence.add_list Egraph.prec [ id ];
      id
  | Some id -> id

let type_of_string (s : string) : Type.t =
  match s with
  | "Int" -> Type.int
  | "Bool" -> Type.prop
  | _ -> failwith (Format.sprintf "unrecognized type %s" s)
(* Type.const (ID.make s) *)

(*
let term_of_sexp  (s : Sexplib.Sexp.t)  : Term.t =
  Term.false_
*)
(*
Term_of_sexp   
*)
let term_of_sexp' (s : Sexplib.Sexp.t) st : Logtk.Term.t =
  let fresh_counter = ref 0 in
  let rec worker gamma s =
    match s with
    | Sexplib.Sexp.Atom a -> (
        match StrMap.get a gamma with
        | Some fvar -> fvar
        | None -> (
            if String.equal a "+" then
              Term.tyapp
                (Term.builtin
                   ~ty:Type.([ tType; int; int ] ==> int)
                   Logtk.Builtin.Sum)
                [ Type.int ]
            else
              let a' = id_of_string a st in
              if Str.string_match (Str.regexp "[0-9]+") a 0 then
                Term.const ~ty:Type.int a'
              else
                match ID.Map.get a' st.types with
                | None ->
                    Term.var_of_int ~ty:Type.int (String.hash a)
                    (* TODO: obviusly, this is idiotic *)
                | Some ty -> Term.const ~ty a'
              (* failwith (Format.sprintf "cannot determine type of %s" a) *)))
    | Sexplib.Sexp.List [ Sexp.Atom "lambda"; Sexp.List vars; body ] ->
        let fvars, gamma =
          List.fold_left
            (fun (fvars, gamma) t_typ ->
              match t_typ with
              | Sexp.List [ Sexp.Atom t; Sexp.Atom ty ] ->
                  let ty = type_of_string ty in
                  let t' =
                    Logtk.HVar.make ~ty !fresh_counter
                    (* Hmm I dunno *)
                  in
                  fresh_counter := !fresh_counter + 1;
                  (t' :: fvars, StrMap.add t (Term.var t') gamma)
              | _ -> failwith "ill formed lambda binder type")
            ([], gamma) vars
        in
        let body = worker gamma body in
        Term.fun_of_fvars fvars body
    | Sexplib.Sexp.List l -> (
        let l = List.map (worker gamma) l in
        match l with
        | [ a ] -> a
        | f :: xs -> Term.app f xs
        | [] -> failwith "empty application")
  in
  worker StrMap.empty s

let run_one egraph (rules : (Term.t * Term.t) list) : Egraph.t =
  Format.printf "run one iter\n";
  let matches =
    List.map
      (fun (lhs, rhs) ->
        Iter.map
          (fun match_ ->
            (* Format.printf "%a ||| %a --> %a    match\n" Logtk.Subst.pp match_
               Term.pp lhs Term.pp rhs; *)
            ( Logtk.Subst.FO.apply Logtk.Subst.Renaming.none match_ (lhs, 0),
              Logtk.Subst.FO.apply Logtk.Subst.Renaming.none match_ (rhs, 0) ))
          (Egraph.ematch egraph lhs))
      rules
  in
  let egraph =
    List.fold_left
      (fun egraph matches_ ->
        Iter.fold
          (fun egraph (lhs, rhs) -> Egraph.union egraph lhs rhs)
          egraph matches_)
      egraph matches
  in
  Egraph.canonize egraph

let term_of_zf_string s st =
  let open Logtk_parsers in
  let untyped = Parse_zf.parse_term Lex_zf.token (Lexing.from_string s) in
  let ctx = Logtk.TypeInference.Ctx.create ~implicit_ty_args:true () in
  let ty_ctx = Type.Conv.create () in
  ID.Map.iter
    (fun id ty ->
      Logtk.TypeInference.Ctx.declare ctx id
        (Type.Conv.to_simple_term ty_ctx ty))
    st.types;
  let typed = Logtk.TypeInference.infer_exn ctx untyped in
  let term = Term.Conv.of_simple_term_exn (Term.Conv.create ()) typed in
  term

let open_forall t =
  let counter = ref 0 in
  let rec worker t =
    match Term.view t with
    | AppBuiltin (Logtk.Builtin.ForallConst, [ t ]) ->
        let ty, _ = Term.open_fun t in
        assert (List.length ty = 1);
        let ty = List.hd ty in
        let t = Term.app t [ Term.var_of_int ~ty !counter ] in
        let t = Logtk.Lambda.beta_red_head t in
        counter := !counter + 1;
        worker t
    | _ -> t
  in
  worker t

let apply_action st = function
  | Assert term ->
      let t = term_of_sexp' term st in
      { st with egraph = Egraph.assert_fact st.egraph t }
  | Union (t1, t2) ->
      let t1 = term_of_sexp' t1 st in
      let t2 = term_of_sexp' t2 st in
      { st with egraph = Egraph.union st.egraph t1 t2 }
  | Function (name, in_types, out_type) ->
      let in_types = List.map type_of_string in_types in
      let out_type = type_of_string out_type in
      let typ = Type.arrow in_types out_type in
      { st with types = ID.Map.add (id_of_string name st) typ st.types }
  | Relation (name, types) ->
      let types = List.map type_of_string types in
      let typ = Type.arrow types Type.prop in
      { st with types = ID.Map.add (id_of_string name st) typ st.types }
  | Print ->
      Format.printf "%a\n" pp_state st;
      st
  | Extract t ->
      let t = term_of_sexp' t st in
      Format.printf "%a --> %a\n" Term.pp t Term.pp (Egraph.find st.egraph t);
      st
  | Run n ->
      let egraph =
        Iter.fold
          (fun e _ -> run_one e st.rewrites)
          st.egraph
          (Iter.int_range ~start:1 ~stop:n)
      in
      { st with egraph }
  | Clear ->
      empty
      (*
  | Rewrite r -> (
      let t = term_of_zf_string r st in
      let t = open_forall t in
      (* Format.printf "%a" Term.pp t; *)
      match Term.view t with
      | Term.AppBuiltin (Logtk.Builtin.Eq, [ lhs; rhs ]) ->
          (* Format.printf "%a" (Term.VarSet.pp Logtk.HVar.pp) (Term.vars lhs);
             Format.printf "%a --> %a " Term.pp lhs Term.pp rhs; *)
          { st with rewrites = (lhs, rhs) :: st.rewrites }
      | _ -> failwith "unexpected rewrite form"
      *)
  | Rewrite (lhs, rhs) ->
      let lhs = term_of_sexp' lhs st in
      let rhs = term_of_sexp' rhs st in
      { st with rewrites = (lhs, rhs) :: st.rewrites }
  | a ->
      failwith
        (Format.sprintf "unhandled action %s"
           (Sexplib.Sexp.to_string_hum (sexp_of_t a)))
(*
| Rule (body, head) -> 

| Extract of term -> s
| Union of (term, term) -> s
| Run i -> s
| Function (name, in_ty, out_ty) -> s
*)

(* Map https://ocaml.org/p/containers/2.0/doc/CCMap/module-type-S/index.html *)

let run_program (actions : t list) : string =
  let egraph = ref empty in
  List.iter
    (fun action ->
      Format.printf "%a\n" pp action;
      egraph := apply_action !egraph action)
    actions;
  "working on string output"

let rec sterm_of_sexp venv sexp =
  let open Logtk.STerm in
  match sexp with
  | Sexp.Atom a -> if StrSet.mem a venv then var a else const a
  | Sexp.List l -> (
      match l with
      (* | [Sexp.Atom "lambda"; vars; body] ->
         Bind (Lambda, ,) *)
      | head :: body ->
          app (sterm_of_sexp venv head) (List.map (sterm_of_sexp venv) body)
      | [] -> failwith "unexpected empty list in sexp")

(* and styp_of_sexp? *)
(*
        match head with
        | "+"
        | "*"
        | 
        *)
