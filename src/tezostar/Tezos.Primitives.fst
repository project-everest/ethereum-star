module Tezos.Primitives
module CI = CryptoInterface

type key = CI.public_key
type signature = CI.signature
type timestamp = int
type tez = nat
type handle = int
type pkeyhash = CI.key_hash

type union a b =
  | L of a
  | R of b

type myMap a b = list (a*b)
type mySet a = list a

val compare_bool: bool -> bool -> int
let compare_bool a b =
  match a, b with
  | false, true -> -1
  | true, false -> 1
  | _ -> 0

val compare_int: int -> int -> int
let compare_int a b =
  if a > b then 1
  else if a = b then 0
  else -1

assume val compare_string: string -> string -> int

assume val compare_tez: tez -> tez -> int

assume val compare_keyhash: pkeyhash -> pkeyhash -> int

assume val compare_timestamp: timestamp -> timestamp -> int

assume val map_fold_left : #partial : Type -> tk : Type -> tv : Type ->
  myMap tk tv -> (f : partial -> tk -> tv -> partial) -> init : partial -> partial

assume val set_fold: #partial : Type -> tk : Type ->
  mySet tk -> (f : partial -> tk -> partial) -> init : partial -> partial

type contract_hash = string // stub

// to move in a file for concrete types
type contract =
  | Default of pkeyhash
  | Originated of contract_hash

open FStar.OrdMap

val is_default: contract -> option pkeyhash
let is_default = function
  | Originated _ -> None
  | Default m -> Some m
