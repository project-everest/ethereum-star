(** This module corresponds to the script_repr file in the alpha
 protocol of the Ocaml code.
 It defines a general representation for data and instructions, which
 is used e.g. for storage and hashing.
 *)
module Tezos.ScriptRepr
open FStar.All

// type of expressions used for serializing data (types, instructions and datatypes)
type expr =
| Int : string -> expr
| String : string -> expr
| Prim : string -> list expr -> expr
| Seq : list expr -> expr

val concat_string : list string -> string

let rec concat_string l = match l with
| [] -> "nil"
| hd::tl -> hd^"::"^(concat_string tl)


val move_refinement: #a:Type -> #p:(a -> Type)
 -> l:list a{forall z. List.Tot.memP z l ==> p z} -> list (x:a{p x})
let rec move_refinement #a #p = function
 | [] -> []
 | hd :: tl -> hd :: move_refinement #a #p tl

val forall_memP_precedes: #a:Type -> l:list a -> Lemma (forall x. List.Tot.memP x l ==> x << l)
let forall_memP_precedes #a l =
 let open FStar.Tactics in
 let open FStar.List.Tot in
 assert_by_tactic (forall x. memP x l ==> x << l)
   (x <-- forall_intro;
    apply_lemma (quote memP_precedes))

val aux: #a:Type -> l:list a -> list (x:a{x << l})
let aux #a l = forall_memP_precedes l; move_refinement l

val expr_to_string : e:expr -> Tot string (decreases e)
let rec expr_to_string = function
 | Int s -> "Int("^s^")"
 | String s -> "String("^s^")"
 | Prim s l -> "Prim("^s^","^(concat_string (List.Tot.map expr_to_string (aux l)))^")"
 | Seq l -> "Seq("^(concat_string (List.Tot.map expr_to_string (aux l)))^")"


type code =
  { code : expr ;
    arg_type : expr ;
    ret_type : expr ;
    storage_type : expr }

type storage =
  { storage : expr ;
    storage_type : expr }

let get_storage (st : storage) = st.storage // accessor because I didn't succeed in inlining it

type script_repr_t = | Script : code -> storage -> script_repr_t
