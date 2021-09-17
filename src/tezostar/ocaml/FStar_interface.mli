open Tezos_ScriptRepr

type ocontext

(* type expr *)
(* type myexpr *)

(* val build_expr : (string -> 'a) -> (string -> 'a) -> *)
(*                (string -> 'a list -> 'a) -> ('a list -> 'a) -> *)
(*                myexpr -> 'a *)
(* val make_int : string -> expr *)
(* val make_string : string -> expr *)
(* val make_prim : string -> expr list -> expr *)
(* val make_seq : expr list -> expr *)

val hash_expr : expr -> string

val ocontext0 : ocontext

val int_of_string : string -> Z.t option

val parse_data : string -> expr option

val parse_contract: ocontext -> string -> (expr*expr*expr*expr (* * Tezos_Definitions.ty * Tezos_Definitions.ty * Tezos_Definitions.ty *)) option

val tez_of_string_as_int64 : string -> Z.t option

