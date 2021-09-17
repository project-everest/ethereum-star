module MyBank

open FStar.Char
open FStar.Seq
open FStar.UInt8
open FStar.Heap

type bytes = seq UInt8.t

type word = b:bytes{length b = 32}

let contract() =
  mstore [0x40uy] [0x60uy];
  let x_1 = pow [0x02uy] [0xE0uy] in
  let x_2 = loadCallData [0x00uy] in 
  let callee = div x_2 x_1 in
  if nonZero (eqw callee [0xEDuy; 0x21uy; 0x24uy; 0x8Cuy]) 
  then 
    begin (*** Withdraw ***)
      let x_5 = pow [0x02uy] [0xA0uy] in
      let x_6 = x_5 - [0x01uy] in
      let sender = loadCaller () in 
      let send = land sender x_6 in
      mstore [0x00uy] send;
      mstore [0x20uy] [0x00uy];
      let address = sha3 [0x00uy] [0x40uy] in
      let balance = sload address in 
      call send [0x00uy] balance [];
      sstore address [0x00uy];
      [] (* returns nothing *)
    end
  else 
  if nonZero (eqw callee [0x57uy; 0xEAuy; 0x89uy; 0xB6uy]) 
  then
    begin (*** Deposit ***)
       let x_20 = pow [0x02uy] [0xA0uy] in
       let x_21 = x_20 - [0x01uy] in
       let sender = loadCaller () in 
       let send = land sender x_21 in
       mstore [0x00uy] send;
       mstore [0x20uy] [0x00uy];
       let address = sha3 [0x00uy] [0x40uy] in
       let balance = sload address in 
       let deposit = loadCallValue () in 
       let newbalance = add balance deposit in
       sstore address newbalance;
       [] (* returns nothing *)
     end
  else
  if nonZero (eqw callee [0xF8uy; 0xF8uy; 0xA9uy; 0x12uy]) 
  then
    begin (*** GetBalance ***)
      let x_29 = pow [0x02uy] [0xA0uy] in
      let x_30 = x_29 - [0x01uy] in
      let sender = loadCaller () in 
      let send = land sender x_30 in
      mstore [0x00uy] send;
      mstore [0x20uy] [0x00uy];
      let address = sha3 [0x00uy] [0x40uy] in
      let balance = sload x_33 in 
      mstore [0x60uy] balance;
      loadLocal [0x60uy] [0x20uy] (* returns 32 bytes *)
    end
  else
    [] (* returns nothing *)
