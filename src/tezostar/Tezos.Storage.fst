(** This module is the analog for storage.ml in the Ocaml code.
  * It models the context as a collection of maps and sets, and
  * it provides accessors for these objects. Function names are kept when
  * they are not too ambiguous, which is not always the case because the
  * hierarchy of modules is flattened.
*)
module Tezos.Storage

open Tezos.Primitives
open Tezos.Definitions
open Tezos.TezRepr
open Tezos.ScriptRepr
open Tezos.Error

// let cmp_contracts c1 c2 =

type global_counter = nat // TODO: check

//TODO: move elsewhere
open FStar.Int32
type int32 = FStar.Int32.t

type storage_contract_global_counter = FStar.OrdMap.ordmap global_counter int32 (compare Nat_key)
type storage_contract_set = FStar.OrdSet.ordset contract cmp_contract
type storage_contract_balance = FStar.OrdMap.ordmap contract tez cmp_contract
type storage_contract_manager = FStar.OrdMap.ordmap contract pkeyhash cmp_contract
type storage_contract_spendable = FStar.OrdMap.ordmap contract bool cmp_contract
type storage_contract_delegatable = FStar.OrdMap.ordmap contract bool cmp_contract
type storage_contract_delegate = FStar.OrdMap.ordmap contract pkeyhash cmp_contract
type storage_contract_counter = FStar.OrdMap.ordmap contract int32 cmp_contract
type storage_contract_code = FStar.OrdMap.ordmap contract code cmp_contract
type storage_contract_storage = FStar.OrdMap.ordmap contract storage cmp_contract
type storage_contract_code_fees = FStar.OrdMap.ordmap contract tez cmp_contract
type storage_contract_storage_fees = FStar.OrdMap.ordmap contract tez cmp_contract


noeq type context = {
  // Contract
  storage_contract_global_counter : storage_contract_global_counter;
  storage_contract_set : storage_contract_set;
  storage_contract_balance : storage_contract_balance;
  storage_contract_manager : storage_contract_manager;
  storage_contract_spendable : storage_contract_spendable;
  storage_contract_delegatable : storage_contract_delegatable;
  storage_contract_delegate : storage_contract_delegate;
  storage_contract_counter : storage_contract_counter;
  storage_contract_code    : storage_contract_code;
  storage_contract_storage : storage_contract_storage;
  storage_contract_code_fees : storage_contract_code_fees;
  storage_contract_storage_fees : storage_contract_storage_fees
}

let context0 : context = {
  storage_contract_global_counter = OrdMap.empty;
  storage_contract_set = OrdSet.empty;
  storage_contract_balance = OrdMap.empty;
  storage_contract_manager = OrdMap.empty;
  storage_contract_spendable = OrdMap.empty;
  storage_contract_delegatable = OrdMap.empty;
  storage_contract_delegate = OrdMap.empty;
  storage_contract_counter = OrdMap.empty;
  storage_contract_code    = OrdMap.empty;
  storage_contract_storage = OrdMap.empty;
  storage_contract_code_fees = OrdMap.empty;
  storage_contract_storage_fees = OrdMap.empty;
}

val get_contract_global_counter : context -> global_counter -> tzresult int32
val get_contract_set : context -> tzresult (OrdSet.ordset contract cmp_contract)
val get_contract_balance : context -> contract -> tzresult tez
val get_contract_manager : context -> contract -> tzresult pkeyhash
val get_contract_spendable : context -> contract -> tzresult bool
val get_contract_delegatable : context -> contract -> tzresult bool
val get_contract_delegate : context -> contract -> tzresult pkeyhash
val get_contract_counter : context -> contract -> tzresult int32
val get_contract_code : context -> contract -> tzresult code
val get_contract_storage : context -> contract -> tzresult storage
val get_contract_code_fees : context -> contract -> tzresult tez
val get_contract_storage_fees : context -> contract -> tzresult tez


val get_from_map: #t1:eqtype -> #t2:eqtype -> #f:(FStar.OrdMap.cmp t1) -> FStar.OrdMap.ordmap t1 t2 f -> x:t1 -> tzresult t2
let get_from_map #t1 #t2 #f m x =
match (FStar.OrdMap.select #t1 #t2 #f x m) with
  | Some v -> return v
  | None -> fail Storage_error


val update_map: #t1:eqtype -> #t2:eqtype -> #f:(FStar.OrdMap.cmp t1) -> FStar.OrdMap.ordmap t1 t2 f -> x:t1 -> y:t2 -> tzresult (FStar.OrdMap.ordmap t1 t2 f)
let update_map #t1 #t2 #f m x y =
return (FStar.OrdMap.update x y m)





let get_contract_global_counter c contract =
get_from_map c.storage_contract_global_counter contract

let get_contract_set c = Ok c.storage_contract_set

let get_contract_balance c contract =
get_from_map c.storage_contract_balance contract

let get_contract_manager c contract =
get_from_map c.storage_contract_manager contract

let get_contract_spendable c contract =
get_from_map c.storage_contract_spendable contract

let get_contract_delegatable c contract =
get_from_map c.storage_contract_delegatable contract

let get_contract_delegate c contract =
get_from_map c.storage_contract_delegate contract

let get_contract_counter c contract =
get_from_map c.storage_contract_counter contract

let get_contract_code c contract =
get_from_map c.storage_contract_code contract

let get_contract_storage c contract =
get_from_map c.storage_contract_storage contract

let get_contract_code_fees c contract =
get_from_map c.storage_contract_code_fees contract

let get_contract_storage_fees c contract =
get_from_map c.storage_contract_storage_fees contract

val delete_from_map: #t1:eqtype -> #t2:Type -> FStar.Map.t t1 t2 -> x:t1 -> tzresult (FStar.Map.t t1 t2)

// let delete_from_map #t1 #t2 m x =
// FStar.Map.restrict

val delete: context -> contract -> tzresult context
let delete c contract = (* TODO *) fail (Unimplemented "Storage.delete")

val update_contract_balance : context -> contract -> tez -> tzresult context
val update_contract_code : context -> contract -> code -> tzresult context
val update_contract_storage : context -> contract -> storage -> tzresult context

let update_contract_balance c contract amount =
newmap <-- update_map c.storage_contract_balance contract amount;
return ({c with storage_contract_balance = newmap})

let update_contract_code c contract code =
newmap <-- update_map c.storage_contract_code contract code;
return ({c with storage_contract_code = newmap})

let update_contract_storage c contract storage =
newmap <-- update_map c.storage_contract_storage contract storage;
return ({c with storage_contract_storage = newmap})


(** Spend [amount] from the account of [contract] *)
val spend_from_script : context -> contract -> tez -> tzresult context

let spend_from_script c contract amount =
  begin
    balance <-- get_contract_balance c contract;
    if balance < amount then fail Balance_too_low else
      let new_balance = balance - amount in
      // TODO: add fees
      update_contract_balance c contract new_balance
  end // TODO: what happens if either get or update does not work? In Tezos, they delete the contract


(** Specification of [spend_from_script] *)
val spend_from_script_correct : c:context -> contract:contract -> am:tez ->
     bal:tez ->
     Lemma
     (requires bal >= am ///\ FStar.Map.contains c.storage_contract_balance contract
     /\ (get_contract_balance c contract = Ok bal))
     (ensures
     (match spend_from_script c contract am with | Error _ -> False | Ok c' ->
     match sub_tez bal am with
     | Ok newb -> get_contract_balance c' contract = Ok newb
     | Error _ -> True))

let spend_from_script_correct ctxt c am bal = ()

(** this function is a generic function for adding a new contract to the
  * storage. It does many things, but for now we will restrict ourselves to
  * simple operations in order not to spend too much time copying the whole
  * codebase before proving anything.
  * For now, the only supported operation is adding the contract's balance
  * to the database of balances [c.storage_contract_balance] *)
val create_base : context -> contract -> balance:tez -> manager:pkeyhash ->
		  delegate:option pkeyhash -> script:option script_repr_t ->
		  spendable:bool -> delegatable:bool -> tzresult context

let create_base c contract bal manager delegate oscript spendable delagatable =
  update_contract_balance c contract bal
  // let scb' = FStar.Map.upd c.storage_contract_balance contract bal in
  // return ({c with storage_contract_balance=scb'})

(** A function to create a default contract (just an account) *)
val create_default: context -> pkeyhash -> tez -> tzresult context

let create_default c manager balance =
  create_base c (Default manager) balance manager (Some manager) None true false

(* this should probably move somewhere else *)
assume val minimal_contract_balance : tez

(** [credit contract contract amount] credits [contract] with [amount]
  * provided the amount is greater than the minimal contract balance *)
val credit : context -> contract -> tez -> tzresult context

let credit c contract amount =
  match FStar.OrdMap.contains contract c.storage_contract_balance with
  | false -> begin
    match is_default contract with
    | None -> fail Non_existing_contract (* this should be a failure *)
    | Some manager ->
      if amount < minimal_contract_balance then
	return c (* burn the tokens *)
      else
	create_default c manager amount
	    end
  | true -> begin
	     b <-- get_contract_balance c contract;
	     new_balance <-- (add_tez b amount);
	     update_contract_balance c contract new_balance
	   end
	   // TODO later: Missing: update roll storage

(** Checks if [contract] exists in the context [c] *)
val exists_contract : context -> contract -> bool

let exists_contract c contract =
match is_default contract with
| Some _ -> true
| None -> false // Placeholder, see contract_storage.ml

val get_script : context -> contract -> tzresult script_repr_t // to refine

let get_script c contract = fail (Unimplemented "Storage.get_script")
                                 // Placeholder, for now we're only
				 // interested in getting the script
				 // of a default account for which
				 // this would be the result
				 // TODO: replace with an error "not implemented"

(** update storage and fees: for now, this function does not do anything *)
val update_script_storage_and_fees : context -> contract -> tez -> expr -> tzresult context

let update_script_storage_and_fees c contract storage_fees storage = return c (* TODO *)

(* same variable as in the OCaml code *)
assume val dummy_storage_fee : nat


/// The following (commented) representation could be used to emulate
/// the whole storage hierarchy of modules, but it is premature for
/// now.


//(** [context] is a single abstract view of the database
//  * All	the key-value stores that we are going to use
//  * will be referencing [context]
//*)
// type accessor_kind =
// | Indexed_data_storage
// | Indexed_optional_data_storage
// | Single_data_storage
// | Data_set_storage
// | Counter_kind

// type storage_type : (k:accessor_kind) -> Type =
// | Ids : (key : FStar.Set.eqtype) -> (value : Type) -> storage_type Indexed_data_storage

// // with the type declaration it does not work..
// // val build_storage_type : #k:accessor_kind -> storage_type k -> Type

// let build_storage_type (#ak:accessor_kind) (sk:storage_type ak) = match sk with
// | Ids k v -> FStar.Map.t k v

// type context_accessors =
// | Roll
// | Contract
// | Vote
// | Public_key
// | Seed
// | Rewards

// type contract_accessors =
// | Global_counter
// | Set
// | Balance
// | Manager
// | Delegate
// | Spendable
// | Delegatable
// | Counter
// | Code
// | Storage
// | Code_fees
// | Storage_fees

// val contract_accessors_kind : contract_accessors -> accessor_kind

// let contract_accessors_kind = function
// | Global_counter -> Counter_kind
// | Set -> Data_set_storage
// | Balance -> Indexed_data_storage
// | Manager -> Indexed_data_storage
// | Delegate -> Indexed_data_storage
// | Spendable -> Indexed_data_storage
// | Delegatable -> Indexed_data_storage
// | Counter -> Indexed_data_storage
// | Code -> Indexed_data_storage
// | Storage -> Indexed_data_storage
// | Code_fees -> Indexed_data_storage
// | Storage_fees -> Indexed_data_storage


// /// TODO eventually: add all the other accessors from storage.mli

// /// Contract

// let contract_balances =	build_storage_type (Ids contract tez)

// // Balance
