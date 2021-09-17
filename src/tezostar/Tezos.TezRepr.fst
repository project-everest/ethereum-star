module Tezos.TezRepr
open Tezos.Error

unfold type tez = nat

val add_tez : tez -> tez -> tzresult tez // actually, result, not option
val sub_tez : tez -> tez -> tzresult tez
val mul_tez : tez -> tez -> tzresult tez
val div_tez : tez -> tez -> tzresult tez

let add_tez v1 v2 = let v = v1 + v2 in
if v < pow2 64 then return v else fail Addition_overflow
let sub_tez v1 v2 =
if v1 <= v2 then return (v2 - v1) else fail Substraction_underflow
let mul_tez v1 v2 = let v= FStar.Mul.(v1 * v2) in if v < pow2 64 then return v else fail Multiplication_overflow
let div_tez v1 v2 = if v2 <= 0 then fail Invalid_divisor else return (v1 % v2)
