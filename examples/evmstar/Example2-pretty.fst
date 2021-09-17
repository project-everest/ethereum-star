module Ex2

open FStar.Char
open FStar.Seq
open FStar.UInt8
open FStar.Heap

type bytes = seq UInt8.t

type word = b:bytes{length b = 32}

(* These hashes identify source functions *)

let withdrawFunction   = [0x5Buy; 0x6Buy; 0x43uy; 0x1Duy]
let getBalanceFunction = [0xF8uy; 0xF8uy; 0xA9uy; 0x12uy]

let mask = [0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy; 0xFFuy]

let contract() =
  mstore [0x40uy] [0x60uy];
  let x_1 = pow [0x02uy] [0xE0uy] in
  let x_2 = loadArg [0x00uy] in
  let callee = x_2 / x_1 in 
  if callee = withdrawFunction then 
    begin 
      let n = loadArg [0x04uy] in
      let balance = sload [0x00uy] in
      if balance > n then [] (* returns with no result *)
      else
        let sender = loadCaller () in
        let send = land sender mask in
        let result =
          match call send [0x00uy] n [] with
          | Some outputs -> one
          | None         -> zero in
        let balance = sload [0x00uy] in
        let newbalance = balance - n in  
        sstore [0x00uy] newbalance;
        []
    end
  else
  if callee = getBalanceFunction then
    begin
      let balance = sload [0x00uy] in
      mstore [0x60uy] balance;
      loadLocal [0x60uy] [0x20uy] (* returns these 32 bytes *)
    end
  else
    [] 
