module Tezos.Examples.Factorial

open Tezos.Primitives
open Tezos.UntypedDefinitions
open Tezos.Interpreter


/// Factorial

(** Inner loop *)
let loop: uinstr =
  (* [ (n <> 0)? ; n; acc ] *)
  (
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
  )

(** Factorial program *)
let factorial: uinstr =
  (* [ n ] -- input parameter, n >= 0 *)
  Dup >>
  (* [ n ; n ] *)
  Eq >>
  (* [ (n = 0)? ; n ] *)
  If ( Drop >>
       (* [] *)
       Const_int 1
       (* [ 1 ] *)
     ) (* return 0! = 1 *)
     ( Const_int 1 >>    (* accumulator's initial value *)
       (* [ 1; n ] *)    (* acc = 1, 0 < n *)
       Swap >>
       (* [ n; 1 ] *)
       Dup >>
       (* [ n; n; 1 ] *)
       Neq >>
       (* [ (n <> 0)?; n; 1 ] *)
       Loop loop >>
       (* [ 0; fact n ] *)
       Drop
       (* [ fact n ] *)
     ) (* return n! *)


let origination : origination_nonce =
  { operation_hash = "dummy";
    origination_index = 1 }

let qta = 100

let orig = Default "orig"

let source = Default "source"

let amount = 0

assume val ctxt0 : Tezos.Storage.context

let test = assert_norm (
  match step origination qta orig source amount ctxt0 factorial (Item (DInt 10) Empty) with
  | Tezos.Error.Ok (Item (DInt 3628800) _, _, _, _) -> True
  | _ -> False)
