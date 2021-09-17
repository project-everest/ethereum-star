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
open BatFormat

open Ast

let hexa = "0123456789ABCDEF"

let of_char c =
  let x = Char.code c in
  let s = Bytes.create 2 in
  Bytes.set s 0 (hexa.[x lsr 4]);
  Bytes.set s 1 (hexa.[x land 0xf]);
  s

let to_char x y =
  let code c =
    match c with
    | '0'..'9' -> Char.code c - 48
    | 'A'..'F' -> Char.code c - 55
    | 'a'..'f' -> Char.code c - 87
    | _ -> failwith (sprintf "Invalid hex digit: %d" (Char.code c))
  in
  Char.chr ((code x) lsl 4 + code y)

let byte_of_opcode = function
  | STOP          -> '\x00'
  | ADD           -> '\x01'
  | MUL           -> '\x02'
  | SUB           -> '\x03'
  | DIV           -> '\x04'
  | SDIV          -> '\x05'
  | MOD           -> '\x06'
  | SMOD          -> '\x07'
  | ADDMOD        -> '\x08'
  | MULMOD        -> '\x09'
  | EXP           -> '\x0A'
  | SIGNEXTEND    -> '\x0B'

  | LT            -> '\x10'
  | GT            -> '\x11'
  | SLT           -> '\x12'
  | SGT           -> '\x13'
  | EQ            -> '\x14'
  | ISZERO        -> '\x15'
  | AND           -> '\x16'
  | OR            -> '\x17'
  | XOR           -> '\x18'
  | NOT           -> '\x19'
  | BYTE          -> '\x1A'

  | SHA3          -> '\x20'

  | ADDRESS       -> '\x30'
  | BALANCE       -> '\x31'
  | ORIGIN        -> '\x32'
  | CALLER        -> '\x33'
  | CALLVALUE     -> '\x34'
  | CALLDATALOAD  -> '\x35'
  | CALLDATASIZE  -> '\x36'
  | CALLDATACOPY  -> '\x37'
  | CODESIZE      -> '\x38'
  | CODECOPY      -> '\x39'
  | GASPRICE      -> '\x3A'
  | EXTCODESIZE   -> '\x3B'
  | EXTCODECOPY   -> '\x3C'

  | BLOCKHASH     -> '\x40'
  | COINBASE      -> '\x41'
  | TIMESTAMP     -> '\x42'
  | NUMBER        -> '\x43'
  | DIFFICULTY    -> '\x44'
  | GASLIMIT      -> '\x45'

  | POP           -> '\x50'
  | MLOAD         -> '\x51'
  | MSTORE        -> '\x52'
  | MSTORE8       -> '\x53'
  | SLOAD         -> '\x54'
  | SSTORE        -> '\x55'
  | JUMP          -> '\x56'
  | JUMPI         -> '\x57'
  | PC            -> '\x58'
  | MSIZE         -> '\x59'
  | GAS           -> '\x5A'
  | JUMPDEST      -> '\x5B'

  | PUSH (n, _)   -> Char.chr (0x5F + n)
  | DUP n         -> Char.chr (0x7F + n)
  | SWAP n        -> Char.chr (0x8F + n)
  | LOG n         -> Char.chr (0xA0 + n)

  | CREATE        -> '\xF0'
  | CALL          -> '\xF1'
  | CALLCODE      -> '\xF2'
  | RETURN        -> '\xF3'
  | DELEGATECALL  -> '\xF4'
  | SUICIDE       -> '\xFF'
  | _             -> failwith "Unknown opcode\n"

let array_of_stream n byte_stream : byte array =
  let a = Array.make n '\x00' in
  let rec read i =
    if i = n then ()
    else
      let b = Stream.next byte_stream in
      Array.set a i b;
      read (i + 1)
  in
  read 0;
  a

let opcode_of_stream byte_stream =
  let b = Stream.next byte_stream in
    if '\x60' <= b && b <= '\x7F' then
      let n = Char.code b - 0x5F in
      let a = array_of_stream n byte_stream in
      PUSH (n, a)
    else if '\x80' <= b && b <= '\x8F' then
      let n = Char.code b - 0x7F in
      DUP n
    else if '\x90' <= b && b <= '\x9F' then
      let n = Char.code b - 0x8F in
      SWAP n
    else if '\xA0' <= b && b <= '\xA4' then
      let n = Char.code b - 0xA0 in
      LOG n
    else match b with
    | '\x00' -> STOP
    | '\x01' -> ADD
    | '\x02' -> MUL
    | '\x03' -> SUB
    | '\x04' -> DIV
    | '\x05' -> SDIV
    | '\x06' -> MOD
    | '\x07' -> SMOD
    | '\x08' -> ADDMOD
    | '\x09' -> MULMOD
    | '\x0A' -> EXP
    | '\x0B' -> SIGNEXTEND

    | '\x10' -> LT
    | '\x11' -> GT
    | '\x12' -> SLT
    | '\x13' -> SGT
    | '\x14' -> EQ
    | '\x15' -> ISZERO
    | '\x16' -> AND
    | '\x17' -> OR
    | '\x18' -> XOR
    | '\x19' -> NOT
    | '\x1A' -> BYTE

    | '\x20' -> SHA3

    | '\x30' -> ADDRESS
    | '\x31' -> BALANCE
    | '\x32' -> ORIGIN
    | '\x33' -> CALLER
    | '\x34' -> CALLVALUE
    | '\x35' -> CALLDATALOAD
    | '\x36' -> CALLDATASIZE
    | '\x37' -> CALLDATACOPY
    | '\x38' -> CODESIZE
    | '\x39' -> CODECOPY
    | '\x3A' -> GASPRICE
    | '\x3B' -> EXTCODESIZE
    | '\x3C' -> EXTCODECOPY

    | '\x40' -> BLOCKHASH
    | '\x41' -> COINBASE
    | '\x42' -> TIMESTAMP
    | '\x43' -> NUMBER
    | '\x44' -> DIFFICULTY
    | '\x45' -> GASLIMIT

    | '\x50' -> POP
    | '\x51' -> MLOAD
    | '\x52' -> MSTORE
    | '\x53' -> MSTORE8
    | '\x54' -> SLOAD
    | '\x55' -> SSTORE
    | '\x56' -> JUMP
    | '\x57' -> JUMPI
    | '\x58' -> PC
    | '\x59' -> MSIZE
    | '\x5A' -> GAS
    | '\x5B' -> JUMPDEST

    | '\xF0' -> CREATE
    | '\xF1' -> CALL
    | '\xF2' -> CALLCODE
    | '\xF3' -> RETURN
    | '\xF4' -> DELEGATECALL
    | '\xFF' -> SUICIDE
    | _ -> failwith (sprintf "Unknown opcode: 0x%x\n" (Char.code b))

let byte_array_to_string =
  IO.to_string
    (Array.print ~first:"" ~last:"" ~sep:""
                 (fun f b -> String.print f (of_char b)))

let opcode_to_string = function
  | STOP          -> "STOP"
  | ADD           -> "ADD"
  | MUL           -> "MUL"
  | SUB           -> "SUB"
  | DIV           -> "DIV"
  | SDIV          -> "SDIV"
  | MOD           -> "MOD"
  | SMOD          -> "SMOD"
  | ADDMOD        -> "ADDMOD"
  | MULMOD        -> "MULMOD"
  | EXP           -> "EXP"
  | SIGNEXTEND    -> "SIGNEXTEND"

  | LT            -> "LT"
  | GT            -> "GT"
  | SLT           -> "SLT"
  | SGT           -> "SGT"
  | EQ            -> "EQ"
  | ISZERO        -> "ISZERO"
  | AND           -> "AND"
  | OR            -> "OR"
  | XOR           -> "XOR"
  | NOT           -> "NOT"
  | BYTE          -> "BYTE"

  | SHA3          -> "SHA3"

  | ADDRESS       -> "ADDRESS"
  | BALANCE       -> "BALANCE"
  | ORIGIN        -> "ORIGIN"
  | CALLER        -> "CALLER"
  | CALLVALUE     -> "CALLVALUE"
  | CALLDATALOAD  -> "CALLDATALOAD"
  | CALLDATASIZE  -> "CALLDATASIZE"
  | CALLDATACOPY  -> "CALLDATACOPY"
  | CODESIZE      -> "CODESIZE"
  | CODECOPY      -> "CODECOPY"
  | GASPRICE      -> "GASPRICE"
  | EXTCODESIZE   -> "EXTCODESIZE"
  | EXTCODECOPY   -> "EXTCODECOPY"

  | BLOCKHASH     -> "BLOCKHASH"
  | COINBASE      -> "COINBASE"
  | TIMESTAMP     -> "TIMESTAMP"
  | NUMBER        -> "NUMBER"
  | DIFFICULTY    -> "DIFFICULTY"
  | GASLIMIT      -> "GASLIMIT"

  | POP           -> "POP"
  | MLOAD         -> "MLOAD"
  | MSTORE        -> "MSTORE"
  | MSTORE8       -> "MSTORE8"
  | SLOAD         -> "SLOAD"
  | SSTORE        -> "SSTORE"
  | JUMP          -> "JUMP"
  | JUMPI         -> "JUMPI"
  | PC            -> "PC"
  | MSIZE         -> "MSIZE"
  | GAS           -> "GAS"
  | JUMPDEST      -> "JUMPDEST"

  | PUSH (n, a)   -> sprintf "PUSH%d %s" n (byte_array_to_string a)
  | DUP  n        -> sprintf "DUP%d" n
  | SWAP n        -> sprintf "SWAP%d" n
  | LOG  n        -> sprintf "LOG%d" n

  | CREATE        -> "CREATE"
  | CALL          -> "CALL"
  | CALLCODE      -> "CALLCODE"
  | RETURN        -> "RETURN"
  | DELEGATECALL  -> "DELEGATECALL"
  | SUICIDE       -> "SUICIDE"

  | NOP           -> "NOP"

let byte_stream_of_channel channel =
  Stream.from
    (fun _ ->
      try
        let a = input_char channel in
        let b = input_char channel in
        Some (to_char a b)
      with End_of_file -> None)

let opcode_stream_of_byte_stream bytes =
  Stream.from
    (fun _ ->
      try
        let c = opcode_of_stream bytes in
        Some c
      with End_of_file -> None)

let parse channel =
  let bytes = byte_stream_of_channel channel in
  let opcodes = opcode_stream_of_byte_stream bytes in
  Array.of_enum (Stream.enum opcodes)

let rec pretty_print outfile =
  Array.iter (fun c ->
    Printf.fprintf outfile "%s\n" (opcode_to_string c))

let pad_with_nop opcodes =
  Array.to_list opcodes |>
  List.map (fun c ->
      match c with
      | PUSH (n,_) ->
         Array.append (Array.make 1 c) (Array.make n NOP)
      | _ -> Array.make 1 c)
  |> Array.concat
