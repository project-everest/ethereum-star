(**
 * Error monad.
 * We don't accumulate an error trace, just a single error.
 *)
module Tezos.Error

type result (a:Type) (b:Type)  =
  | Ok of a
  | Error of b

type error =
/// General
  | Unimplemented of string
  | GenericError of string
/// Interpreter
  | Quota_exceeded
  | Reject
  | Runtime_contract_error of string
/// Storage
  | Storage_error
  | Balance_too_low
  | Non_existing_contract
/// Guarded Arithmetic
  | Addition_overflow
  | Substraction_underflow
  | Multiplication_overflow
  | Negative_multiplicator
  | Invalid_divisor

val error_to_string : error -> string

let error_to_string = function
  | Unimplemented s -> "Unimplemented: "^s
  | GenericError s ->  "Generic Error: "^s
  | Quota_exceeded -> "Quota_exceeded"
  | Reject -> "Reject"
  | Runtime_contract_error s -> ("Runtime_contract_error: "^s)
  | Storage_error -> "Storage_error"
  | Balance_too_low -> "Balance_too_low"
  | Non_existing_contract -> "Non_existing_contract"
  | Addition_overflow -> "Addition_overflow"
  | Substraction_underflow -> "Substraction_underflow"
  | Multiplication_overflow -> "Multiplication_overflow"
  | Negative_multiplicator -> "Negative_multiplicator"
  | Invalid_divisor -> "Invalid_divisor"


type tzresult a = result a error

val return: #a:Type -> a -> tzresult a
let return #a x = Ok x

val bind: #a:Type -> #b:Type -> tzresult a -> (a -> tzresult b) -> tzresult b
let bind #a #b res f =
  match res with
  | Ok x -> f x
  | Error e -> Error e

val fail: #a:Type -> error -> tzresult a
let fail #a e = Error e
