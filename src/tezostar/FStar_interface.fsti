module FStar_interface

module SR = Tezos.ScriptRepr

assume new type ocontext // OCaml context

val ocontext0 : ocontext

val hash_expr : SR.expr -> string

val int_of_string : string -> option int

val parse_data : string -> option SR.expr

val parse_contract: ocontext -> string
  -> option (SR.expr * SR.expr * SR.expr * SR.expr (* *ty*ty*ty *) )

val tez_of_string_as_int64 : string -> option int
