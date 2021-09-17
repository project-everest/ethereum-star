(*
   Copyright 2016 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
open Batteries
open BatList
open Ast

(* from pages 20-21 of yellow paper *)
let g_zero = 0
let g_base = 2
let g_verylow = 3
let g_low = 5
let g_mid = 8
let g_high = 10
let g_ext = 20
let g_sload = 50
let g_jumpdest = 1
let g_create = 32000

let g_expbyte = 10
let g_copy = 3

let g_log = 375
let g_logdata = 8

let g_sset = 20000

type simpleCost = Nop | Create | Jumpdest | Sload | Zero | Base | Verylow | Low | Mid | High | Ext

let in_w_zero op = List.mem op [STOP;SUICIDE;RETURN]
let in_w_base op = List.mem op [ADDRESS;ORIGIN;CALLER;CALLVALUE;CALLDATASIZE;CODESIZE;GASPRICE;COINBASE;TIMESTAMP;NUMBER;DIFFICULTY;GASLIMIT;POP;PC;MSIZE;GAS]
(* MLOAD, MSTORE, MSTORE8 and CALLDATALOAD have been remove from in_w_verylow *)
(* because their gas cost is already handled in F* *)
let in_w_verylow op =
  List.mem op [ADD;SUB;NOT;LT;GT;SLT;SGT;EQ;ISZERO;AND;OR;XOR;BYTE] ||
    match op with
    | PUSH(i,_) -> 1 <= i && i <= 32
    | DUP(i) -> 1 <= i && i <= 32
    | SWAP(i) -> 1 <= i && i <= 32
    | _ -> false

let in_w_low op = List.mem op [MUL;DIV;SDIV;MOD;SMOD;SIGNEXTEND]
let in_w_mid op = List.mem op [ADDMOD;MULMOD;JUMP]
let in_w_high op = op = JUMPI
let in_w_ext op = List.mem op [BALANCE;EXTCODESIZE;BLOCKHASH]

let get_cost_category op =
  match op with
  | NOP -> Some Nop
  | CREATE -> Some Create
  | JUMPDEST -> Some Jumpdest
  | SLOAD -> None (* gas cost for SLOAD is now handled in F* directly *)
  | op ->
  try (Some
  (if in_w_zero op then Zero else
    if in_w_base op then Base else
      if in_w_verylow op then Verylow else
	if in_w_low op then Low else
	  if in_w_mid op then Mid else
	    if in_w_high op then High else
	      if in_w_ext op then Ext else
		failwith "Not a simple cost operand" ))
       with | _ -> None

let category_to_cost cat =
  match cat with
  | Nop -> 0
  | Create -> g_create
  | Jumpdest -> g_jumpdest
  | Sload -> g_sload
  | Zero -> g_zero
  | Base ->  g_base
  | Verylow ->  g_verylow
  | Low ->  g_low
  | Mid -> g_mid
  | High -> g_high
  | Ext ->  g_ext
