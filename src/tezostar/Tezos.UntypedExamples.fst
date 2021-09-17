module Tezos.UntypedExamples

open Tezos.Definitions
open Tezos.UntypedDefinitions
open Tezos.Serialization
open Tezos.Storage
open Tezos.AbstractInterpreter
open Tezos.Interpreter

// open Tezos.LanguageGadt

assume val ctxt0 : context

/// Examples from michelson-lang.com

/// Identity contract (not sure how to write this in our case)
// parameter string;
// return string;
// storage unit;
// code {};

///  Contract which sends money to anyone

// parameter key;
// return unit;
// storage unit;
// code {CAR; DEFAULT_ACCOUNT; # Create an account for the recipient of the funds
//       DIP{UNIT};             # Push a value of the storage type below the contract
//       PUSH tez "1.00";       # The person can have a ꜩ
//       UNIT;                 # Push the contract's argument type
//       TRANSFER_TOKENS;      # Run the transfer
//       PAIR};                # Cleanup and put the return values

let anyone_contract = Car >> Default_account >> Dip (Const_unit) >> Const_tez 100 (* "1.00" in the original code *) >> Const_unit >> Transfer_tokens Unit_t >> Cons_pair


let anyone_param = Key_t
let anyone_return = Unit_t
let anyone_storage = Unit_t
let anyone_input = Pair_t anyone_param anyone_storage
let anyone_output = Pair_t anyone_return anyone_storage

let output_type_ac = parse_uinstr ctxt0 anyone_contract	(Item_t (anyone_input) Empty_t)

let _ = assert_norm (output_type_ac == Typed (Item_t anyone_output Empty_t))
 (* (input,storage) --> (return,storage) *)

/// Examples from AbstractInterpreter


let v = parse_uinstr ctxt0 (Seq Dup Drop) (Item_t Int_t Empty_t)

let (>>) = Seq

val ufactorial : uinstr

let ufactorial =
  (* [ n ] -- input parameter, n >= 0 *)
  Dup >>
  (* [ n ; n ] *)
  Eq >>
  (* [ (n = 0)? ; n ] *)
  If ( Drop >>
	(* [] *)
	Const_int 1
	(* [ 1 ] *) )        (* return 0! = 1 *)
      ( Const_int 1 >>    (* push accumulator's initial value *)
	(* [ acc ; n ] *)    (* acc = 1, n <> 0 *)
	Swap >>
	(* [ n ; acc ] *)
	Dup >>
	(* [ n ; n ; acc ] *)
	Neq >>
	(* [ (n <> 0)? ; n; acc ] *)
	Loop (
	  (* [ n ; acc ] *)
	  Dup >>
	  (* [ n ; n ; acc ] *)
	  Dip ( Mul_intint ) >>
	  (* [ n ; n * acc ] *)
	  Const_int 1 >>
	  (* [ 1 ; n ; n * acc ] *)
	  Swap >>
	  (* [ n ; 1 ; n * acc ] *)
	  Sub_int >>
	  (* [ n-1 ; n * acc ] *)
	  Dup >>
	  (* [ n-1 ; n-1 ; n * acc ] *)
	  Neq
	  (* [ (n-1 <> 0)? ; n-1 ; n * acc ] *)
	)  >>
	(* [ 0 ; acc ] *)
	Drop
	(* [ acc ] *) )

let v1 =
  assert_norm (
    parse_uinstr ctxt0 ufactorial (Item_t Int_t Empty_t) ==
    Typed (Item_t Int_t Empty_t))

let v1' = ueval 300 ufactorial (UItem (DInt 30) UEmpty) ctxt0

// let v1'_correct =
//   assert_norm (Partial? v1' /\
//                Partial?.st v1' == UItem (DInt 265252859812191058636308480000000) UEmpty)

let print_partial (v:result) : All.ML unit =
  match v with
  | Partial _ _ (UItem (DInt i) UEmpty) -> IO.print_string ((string_of_int i) ^ "\n")
  | _ -> ()

// let _ = print_partial v1'

/// factorial obtained by stripping the typed one

open Tezos.Translation

let fact_stripped = strip Tezos.TypedExamples.factorial
let v2 = ueval 100 fact_stripped (UItem (DInt 5) UEmpty)
