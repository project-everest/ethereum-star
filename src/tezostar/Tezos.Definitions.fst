module Tezos.Definitions

module P = Tezos.Primitives

open Tezos.TezRepr
open Tezos.Primitives

type comparable_ty =
  | Int_key
  | Nat_key
  | String_key
  | Tez_key
  | Bool_key
  | Key_hash_key
  | Timestamp_key

type ty =
  | Unit_t
  | Int_t
  | Nat_t
  | Signature_t
  | String_t
  | Tez_t
  | Key_hash_t
  | Key_t
  | Timestamp_t
  | Bool_t
  | Pair_t     : ta:ty -> tb:ty -> ty
  | Union_t    : ta:ty -> tb:ty -> ty
  | Map_t      : tk:comparable_ty -> tv:ty -> ty
  | Set_t      : ts:comparable_ty -> ty
  | Option_t   : tv:ty -> ty
  | Lambda_t   : ta:ty -> tb:ty -> ty
  | Contract_t : targ:ty -> tret:ty -> ty
  | List_t     : ta:ty -> ty

let is_comparable =
 function
 | Int_t | Nat_t | String_t | Tez_t | Bool_t | Key_hash_t | Timestamp_t -> true
 | _ -> false

let ty_of_comp_ty =
  function
  | Int_key -> Int_t
  | Nat_key -> Nat_t
  | String_key -> String_t
  | Tez_key -> Tez_t
  | Bool_key -> Bool_t
  | Key_hash_key -> Key_hash_t
  | Timestamp_key -> Timestamp_t

let comp_ty_of_ty (t:ty{is_comparable t}) =
  match t with
  | Int_t -> Int_key
  | Nat_t -> Nat_key
  | String_t -> String_key
  | Tez_t -> Tez_key
  | Bool_t -> Bool_key
  | Key_hash_t -> Key_hash_key
  | Timestamp_t -> Timestamp_key

let interp_comp_ty =
  function
  | Int_key -> int
  | Nat_key -> nat
  | String_key -> string
  | Tez_key -> tez
  | Bool_key -> bool
  | Key_hash_key -> pkeyhash
  | Timestamp_key -> timestamp

type stack_ty : Type =
  | Item_t  : t:ty -> rest:stack_ty -> stack_ty
  | Empty_t : stack_ty

let stackify ta = Item_t ta Empty_t

type typed_contract =
  | TC: ty -> ty -> contract -> typed_contract

let rec string_of_ty = function
  | Unit_t -> "Unit_t"
  | Int_t -> "Int_t"
  | Nat_t -> "Nat_t"
  | Signature_t -> "Signature_t"
  | String_t -> "String_t"
  | Tez_t -> "Tez_t"
  | Key_hash_t ->  "Key_hash_t"
  | Key_t -> "Key_t"
  | Timestamp_t -> "Timestamp_t"
  | Bool_t -> "Bool_t"
  | Pair_t ta tb -> "Pair_t "^(string_of_ty ta)^" "^(string_of_ty tb)
  | Union_t ta tb -> "Union_t "^(string_of_ty ta)^" "^(string_of_ty tb)
  | Map_t tk tv -> "Map_t" (* TODO: improve *)
  | Set_t ts -> "Set_t" (* TODO: improve *)
  | Option_t t -> "Option_t "^(string_of_ty t)
  | Lambda_t ta tb -> "Lambda_t" (* TODO: improve *)
  | Contract_t ta tb -> "Contract_t" (* TODO: improve*)
  | List_t t -> "List_t "^(string_of_ty t)

let string_of_key = function
  | Int_key -> "Int_key"
  | Nat_key -> "Nat_key"
  | String_key -> "String_key"
  | Tez_key -> "Tez_key"
  | Bool_key -> "Bool_key"
  | Key_hash_key -> "Key_hash_key"
  | Timestamp_key -> "Timestamp_key"

val compare_comparable: t:comparable_ty -> x:interp_comp_ty t -> y:interp_comp_ty t -> int
let compare_comparable t x y =
 match t with
 | Int_key -> compare_int x y
 | Nat_key -> compare_int x y
 | String_key -> compare_string x y
 | Tez_key -> compare_tez x y
 | Bool_key -> compare_bool x y
 | Key_hash_key -> compare_keyhash x y
 | Timestamp_key -> compare_timestamp x y

val compare: t:comparable_ty -> OrdMap.cmp (interp_comp_ty t)
let compare t =
 let f = fun x y -> compare_comparable t x y <= 0 in
 // TODO: remove when all compare_xxx functions are defined
 assume (OrdMap.total_order (interp_comp_ty t) f);
 f

val cmp_contract : FStar.OrdMap.cmp contract

let cmp_contract =
  let f c1 c2 =
    match c1, c2 with
    | Default p1, Default p2 -> compare Key_hash_key p1 p2
    | Originated c1, Originated c2 -> compare String_key c1 c2
    | Default _, Originated _ -> false
    | Originated _, Default _  -> false
  in
  assume(OrdMap.total_order contract f);
  f
