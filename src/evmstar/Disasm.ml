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
open Ast
open Parse
open Printf
open GasCost

let gas_flag = ref false
let print_const_flag = ref true
let emit_code s = printf s

type cte = byte array (* of size 1..32 *)

let big_int_of_bytes (c : byte array) =
  let n = Array.length c in
  assert(n <= 32);
  let res = ref Big_int.zero in
  for i = 0 to n-1 do
    res := Big_int.add (Big_int.mul (Big_int.of_int (1 lsl 8)) !res) (Big_int.of_int (int_of_char c.(i)));
  done;
  !res

let int_of_bytes c =
  let n = Array.length c in
  assert(n <= 32);
  let res = ref 0 in
  for i = 0 to n-1 do
    res := (1 lsl 8) * !res + (int_of_char c.(i));
  done;
  !res

let bytes_of_big_int i : cte =
  let rec aux res = function
    | x when Big_int.equal x Big_int.zero -> res
    | k -> let q = Big_int.div k (Big_int.of_int 256) in
           let r = Big_int.sub k (Big_int.mul q (Big_int.of_int 256)) in
           aux (r::res) q
  in let res = Array.map (fun x -> char_of_int (Big_int.to_int x)) (Array.of_list (aux [] i)) in
     assert(Array.length res <= 32);
     res

let bytes_of_int i : cte =
  let rec aux res = function
    | 0 -> res
    | k -> let q = k / 256 in
           let r = k - (q * 256) in
           aux (r::res) q
  in let res = Array.map (char_of_int) (Array.of_list (aux [] i)) in
     assert(Array.length res <= 32);
     res

type address = int (* refinable *)

let addressBytes code c : address =
  let a = int_of_bytes c in
  if a < Array.length code && 0 <= a
  then
    ( if code.(a) <> JUMPDEST then printf "  (* WARNING: %d is not a dest. *)\n" a;
      a)
  else failwith (sprintf "out-of-range code address: %d" a)

let final = function (* removed JUMPI | JUMPDEST *)
  | RETURN | JUMP | JUMPI | STOP | SUICIDE -> true
  | _ -> false

type v =
  | Void of int     (* uninitialized, with intial depth *)
  | Arg of int      (* used as value, with initial depth *)
  | Local of int    (* held in some register *)
  | Constant of cte (* immediate *)

let sprintv = function
  | Void i      -> sprintf "void_%d" i
  | Local i     -> sprintf "x_%d" i
  | Arg i       -> sprintf "arg_%d" i
  | Constant c ->
     let i = big_int_of_bytes c in
     let c = Array.map (fun b -> "0x" ^ (of_char b) ^ "uy") c in
     (IO.to_string (Array.print ~first:"[" ~last:"]"
                               String.print) c)^
     (if !print_const_flag then sprintf " (* %s *) " (Big_int.to_string i) else "")

(* the flag indicates whether the cell was used as a jump destination *)
type cell =
  { mutable contents: v;  (* updated to keep track of access, e.g. from Void i to Arg i *)
    mutable jumped: bool; (* set as we jump to that value, seen as a code address *)
  }

let sprintc (r:cell) =  sprintv r.contents

type s = cell list

let dummy i: cell = { contents = Void i; jumped = false }

let jumpable c =
  match c.contents with
  | Constant _ | Arg _ | Void _ -> c.jumped <- true; c.contents
  | _                           -> failwith "peculiar jump"

let stack0 () = List.init 16 dummy

let fresh =
  let c = ref 0 in
  fun () -> incr c; { contents = Local !c; jumped = false }

let intConst i =
  let v = bytes_of_int i in
  ref (Constant v), false

let one = intConst 0
let zero = intConst 1

let rec write (s:s) x i =
  match s with
  | z::s -> if i = 0 then x::s else z::write s x (i - 1)
  | []   -> failwith "write: stack underflow"

let getCostLog (log_op : opcode) (y : cell) =
  let factor = match log_op with
    | LOG(i) -> i
    | _ -> failwith "not a log opcode" in
  sprintf "%d + %d * %s + %d * g_logtopic" g_log g_logdata (sprintc y) factor

let exp_gas (y:cell) =
  match y.contents with
  | Constant v ->
    let y = int_of_bytes v in
    let l = log (float_of_int y) in
    let c = int_of_float (floor (l /. (log 256.0))) in
    sprintf "%d" (g_expbyte * (1 + c))
  | _ ->
    sprintf "(%d * (1+ floor (log %s)))"g_expbyte (sprintc y)

let step (s: s) (accumulated_gas,list_opcodes) opcode : s * int * opcode list =
  let (new_accumulated_gas,new_list_opcodes) =
  (match get_cost_category opcode with
  | Some cat -> let cost = (category_to_cost cat) in
		(cost + accumulated_gas,opcode::list_opcodes)
  | None ->
    if !gas_flag && list_opcodes <> [] then
      (match accumulated_gas with
    | 0 ->
      printf "  (* burn %d (* opcodes: %s *) *);\n" accumulated_gas (String.concat ", " (List.map opcode_to_string (List.rev list_opcodes)))
    | accumulated_gas ->
      printf "  burn %d (* opcodes: %s *);\n" accumulated_gas (String.concat ", " (List.map opcode_to_string (List.rev list_opcodes)))); (0,[])) in
  let new_stack =
  (* emit_code"  (* depth %d *)\n" (List.length s); *)
  match opcode, s with (* FIXME : put actually working 256 bit integer operations instead of ocaml native operations *)
  | ADD,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = add %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | MUL,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = mul %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | SUB,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = sub %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | DIV,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = div %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | SDIV,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = if %s=0 then  0 \n
			else if %s = -2**255 && %s = -1 then \n
			else %s/%s in \n" (sprintc z) (sprintc y) (sprintc x) (sprintc y) (sprintc x) (sprintc y);
    z::s

  | MOD,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = if %s=0 then 0 else %s mod %s in\n" (sprintc z) (sprintc y) (sprintc x) (sprintc y);
    z::s

  | SMOD,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = if %s=0 then 0 else %s mod %s in\n" (sprintc z) (sprintc y) (sprintc x) (sprintc y);
    z::s

  | ADDMOD,  (u::x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = if %s=0 then 0 else (%s+%s) mod %s in\n" (sprintc z) (sprintc y) (sprintc u) (sprintc x) (sprintc y);
    z::s
  | MULMOD,  (u::x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = if %s=0 then 0 else (%s * %s) mod %s in\n" (sprintc z) (sprintc y) (sprintc u) (sprintc x) (sprintc y);
    z::s

  | EXP,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = pow %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | SIGNEXTEND,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = sign_extend %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | LT,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = %s < %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | GT,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = %s > %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | SLT,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = %s < %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | SGT,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = %s > %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | EQ, (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = eqw %s %s in \n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | ISZERO, (x::s) ->
    let z = fresh () in
    emit_code  " let %s = %s=zero in\n" (sprintc z) (sprintc x);
    z::s

  | AND,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = land %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | OR,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = lor %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | XOR,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = lxor %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | NOT,  (x::s) ->
    let z = fresh () in
    emit_code "  let %s = lnot %s in\n" (sprintc z) (sprintc x);
    z::s

  | BYTE,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = extract_byte %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s
  | SHA3,  (x::y::s) ->
    let z = fresh () in
    emit_code "  let %s = sha3 %s %s in\n" (sprintc z) (sprintc x) (sprintc y);
    z::s

  | ADDRESS,  (s) -> (* TODO: understand how contextual information is represented/accessed *)
    let z = fresh () in
    emit_code "   let %s = get_address () in\n" (sprintc z);
    z::s

  | BALANCE,  (x::s) ->
    let z = fresh () in
    emit_code "   let accountexists = does_account_exist (%s mod 2**160) in\n
                   let %s = if accountexists then (get_balance %s) else 0  in\n" (sprintc z) (sprintc x) (sprintc x);
    z::s

  | ORIGIN,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_origin () in \n" (sprintc z);
    z::s

  | CALLER,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_caller () in \n" (sprintc z);
    z::s

  | CALLVALUE,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_callvalue () in \n" (sprintc z);
    z::s

  | CALLDATASIZE,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_calldatasize () in \n" (sprintc z);
    z::s

  | CALLDATALOAD,  (x::s) ->
    let z = fresh () in
    emit_code "  let %s = get_calldataload %s in \n" (sprintc z) (sprintc x);
    z::s
  | CALLDATACOPY,  (x::y::z::s) ->
    emit_code "  burn (%d * (ceil (%s/32))); \n" g_copy (sprintc y);
    emit_code "  calldatacopy %s %s %s;\n" (sprintc x) (sprintc y) (sprintc z);
    s
  | CODESIZE,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_codesize () in \n" (sprintc z);
    z::s
  | CODECOPY,  (x::y::z::s) ->
    emit_code "  burn (%d* (ceil (%s/32))); \n" g_copy (sprintc y);
    emit_code "  codecopy %s %s %s;\n" (sprintc x) (sprintc y) (sprintc z);
    s
  | GASPRICE,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_gasprice () in \n" (sprintc z);
    z::s

  | EXTCODESIZE,  (x::s) ->
    let z = fresh () in
    emit_code "  let %s = get_extcodesize %s in \n" (sprintc z) (sprintc x);
    z::s

  | EXTCODECOPY,  (u::x::y::z::s) ->
    emit_code "  burn (%d * (ceil (%s/32))); \n" g_copy (sprintc y);
    emit_code "  extcodecopy %s %s %s %s;\n" (sprintc u) (sprintc x) (sprintc y) (sprintc z);
    s

  | NOP, (s) -> s

  (* Block Information *)

  | BLOCKHASH,  (x::s) ->
    let z = fresh () in
    emit_code "  let %s = get_blockhash %s in \n" (sprintc z) (sprintc x);
    z::s

  | COINBASE,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_coinbase () in \n" (sprintc z);
    z::s

  | TIMESTAMP,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_timestamp () in \n" (sprintc z);
    z::s

  | NUMBER,  (s) ->
    let z = fresh () in
    emit_code "  let %s = get_blocknumber () in \n" (sprintc z);
    z::s

  | DIFFICULTY, (s) ->
    let z = fresh () in
    emit_code "  let %s = get_blockdifficulty () in \n" (sprintc z);
    z::s

  | GASLIMIT, (s) ->
    let z = fresh () in
    emit_code "  let %s = get_blockgaslimit () in \n" (sprintc z);
    z::s

  (* Load/store *)

  | MSTORE, (x::y::s) -> emit_code "  mstore %s %s;\n" (sprintc x) (sprintc y); s
  | MSTORE8, (x::y::s) -> emit_code "  mstore8 %s (%s mod 256);\n" (sprintc x) (sprintc y); s
  | SSTORE, (x::y::s) -> emit_code "  sstore %s %s;\n" (sprintc x) (sprintc y); s
  | MLOAD, (x::s) ->
    let z = fresh () in
    emit_code "  let %s = mload %s in \n" (sprintc z) (sprintc x);
    z::s
  | SLOAD, (x::s) ->
    let z = fresh () in
    emit_code "  let %s = sload %s in \n" (sprintc z) (sprintc x);
    z::s
  | POP, (x::s) ->
    s
  | LOG i, (x::y::s) ->
	emit_code "  burn %s; (* opcode LOG %d *)" (getCostLog opcode y) i;
	x::y::(BatList.take i  s)
  |JUMPDEST, s -> 
        s
(*
  | JUMPI, (a::b::s1) ->
      begin
        match jumpable a with
        | Constant c -> 
			let _ = if !gas_flag then printf "burn %d (* opcode %s *);\n" g_high (opcode_to_string opcode) in
			let a = addressBytes code c in
                        printf "  if %s then\n  begin (* offset: %d *)\n";
                        let s2 = step a in
                        printf "  end\n  else\n  begin (* offset: %d *)\n";
                        let s3 = step (j+1) in
                        printf "  end\n\n";
                        s2
        | _          -> s1, failwith "branching into the unknown"
      end
 *)
  | PC, s -> let z = fresh () in
        emit_code "  let %s = get_pc () in\n" (sprintc z);
	z::s
  | GAS, s -> let z = fresh () in
        emit_code "  let %s = get_gas () in\n" (sprintc z);
	z::s
  | MSIZE, s -> let z = fresh () in
        emit_code "  let %s = get_msize () in\n" (sprintc z);
	z::s
  | PUSH (n,c), s -> { contents = Constant c; jumped = false }::s
  | DUP i,       s when List.length s > i -> (List.nth s (i-1))::s
  | SWAP i, (x::s) when List.length s > i -> (List.nth s (i-1))::write s x (i-1)

  | CALL, inGas::target::inValue::inStart::inSize::outStart::outSize::s ->
    let z = fresh() in
    emit_code "  let inputs = loadLocal %s %s in\n" (sprintc inStart) (sprintc inSize);

    (* TODO: add Gcallstipend to inGas to get actual callgas *)
    (* Remark: typo in yellow paper in case no gas provided, p.29 *)
    (* We want to get new suicides as side effects *)
    emit_code "  let (result,gasLeft) = call %s %s %s inputs in\n" (sprintc target) (sprintc inGas) (sprintc inValue);
    emit_code "  let %s = \n" (sprintc z);
    emit_code "    match result with\n";
    emit_code "    | Some outputs -> localStore %s %s outputs; one\n" (sprintc outStart) (sprintc outSize);
    emit_code "    | None         -> zero in\n";
    z::s

  (* catching both final opcodes and short stacks *)
  | op, s -> printf "TODO: %s\n" (opcode_to_string op); s  (* was: failwith "bad step" *)
  in
  let new_list_opcodes =
    List.filter (fun o -> o <> NOP) new_list_opcodes
  in (new_stack,new_accumulated_gas,new_list_opcodes)

type b = opcode list

let rec run_aux code s0 a (gas,list_opcodes) =
  if a < Array.length code
  then
    let opcode = Array.get code a in
    if final opcode then (s0, a)
    else
      let (s1,gas,list_opcodes) = step s0 (gas,list_opcodes) opcode in
      run_aux code s1 (a+1) (gas,list_opcodes)
  else failwith "unterminated code block"

let run code s0 a = run_aux code s0 a (0,[])

type exitInfo =
  (* Local Return *)
  (* s0 suggests the calling convention (but not the callee) *)
  | Return of int
  (* local unconditional branch OR local call; hard to tell *)
  | Branch of address
  | Branch2 of address * address (* local branch; probably not a local call *)
  | ContractReturn
  | Stop
  | Suicide

let stringInfo = function
  | Return i -> sprintf "Return s[%d]" i
  | Branch i -> sprintf "Branch <%d>" i
  | Branch2 (i,j) -> sprintf "Branch2 <%d,%d>" i j
  | ContractReturn -> sprintf "ContractReturn"
  | Stop -> sprintf "Stop"
  | Suicide -> sprintf "Suicide"

type summary = {
  entry:string;
  s0:s;
  s1:s;
  exit:exitInfo
}

module Blocks = Map.Make(struct type t = int let compare = compare end)
let blocks = ref Blocks.empty

let rec summarize s0o code hint i : summary =
  let s0 = match s0o with Some s -> s | None -> stack0 () in
  let s1, j = run code s0 i in
  let s2, exit =
    (* TODO: printf the resulting final F* expressions in all cases, once we have the calling conventions. *)
  let opcode = Array.get code j in
  (match get_cost_category opcode with
  | Some cat -> let cost = (category_to_cost cat) in if !gas_flag then (match cost with
    | 0 -> printf "  (*  burn %d (* opcode %s *) *)\n" cost (opcode_to_string opcode)
    | cost ->  printf "  burn %d (* opcode %s *);\n" cost (opcode_to_string opcode))
  | None -> ());
    match opcode, s1 with
    | JUMP,     (a::s1) ->
      begin
        match jumpable a with
        | Void depth -> emit_code"  %s\n\n" (sprintc (List.nth s1 0));
                        s1, Return depth
        | Constant c -> let a = addressBytes code c in
                        (* let z = fresh () in *)
                        (* emit_code "  let %s = f_%d %s in\n" (sprintc z) a (sprintc (List.nth s1 1)); *)
                        (* and splice the return continuation below *)
                        let sum = summarize (Some s1) code "concolic" a in
                        sum.s1, sum.exit
        | _          -> failwith "jumping into the unknown"
      end
    | JUMPI, (a::b::s1) ->
      begin
        match jumpable a with
        | Constant c -> begin
                        let a = addressBytes code c in
                        emit_code "  if nonZero %s then\n  begin (* offset: %d *)\n" (sprintc b) a;
                        let r_true = summarize (Some s1) code "then" a in
                        emit_code "  end\n  else\n  begin (* offset: %d *)\n" (j+1);
                        let r_false = summarize (Some s1) code "else" (j+1) in
                        emit_code "  end\n";
                        match r_true.exit, r_false.exit with (* fixme! *)
                        | (ContractReturn | Stop | Suicide), _ -> r_false.s1, r_false.exit
                        | _                                    -> r_true.s1, r_true.exit
                        end
                        (* was: s1, Branch2(a,j+1) *)
        | _          -> s1, failwith "branching into the unknown"
      end
    | RETURN, start::size::s ->
                        emit_code"  loadLocal %s %s (* returned outputs *)\n" (sprintc start) (sprintc size);
                        s1, ContractReturn (* TODO: see horrible CALLing convention above *)

    | STOP,   _      -> emit_code"   [] (* no returned outputs *)\n";
                        s1, Stop
    | SUICIDE, _     -> printf"  failwith \"SUICIDE\"\n";
                        s1, Suicide
    | op, _          -> failwith ("not a final opcode: " ^ opcode_to_string op) in
  { entry = hint; s0 = s0; s1 = s2; exit = exit }

(* decomposes code into basic blocks, each with a stack summary *)
(* an index is an entry point if  *)
(* (0) it is 0, or *)
(* (1) it contains JUMPDEST, or *)
(* (2) it is the argument of a PUSH4 just before a JUMP   *)
(* We start with (1), as we need to propagate calling conventions backward.  *)

(* We treat conditional jumps as terminators too,  *)
(* treating the "then" and "else" branches as separate blocks, *)
(* so we need an extra case (3) for the fall-through continuation. *)

(* We do not yet treat fall-through joins, such as  *)
(*       if (b) {br join;}  *)
(*       ... do stuff *)
(* join: ... do more.  *)

let scan code =
  let parse hint i =
    if not(Blocks.mem i !blocks) then
      begin
        if i > 0
        then emit_code "let f_%d () =\n" i (* missing arguments, mutual recursion, ... *)
        else emit_code "let contract() =\n";
        let sum = summarize None code hint i in
        printf "(* block ending with %s *)\n" (stringInfo sum.exit);
        blocks := Blocks.add i sum !blocks
      end in

  (* not used anymore:
  let staticJump i =
     if i > 0
     then
       match Array.get code (i-1) with
       | PUSH (n,c) -> Some (addressBytes code c)  (* do we need to enforce Array.length a = 4? *)
       | _      -> None
     else None in *)

  parse "init" 0;

  (* no need, until we actually build the CFG. 
  for i = 0 to Array.length code - 1 do
    if Array.get code i = JUMPDEST then parse "dest" i;
    if i > 0 && Array.get code (i-1) = JUMPI then parse "else" i
  done
   *)
(* after running scan, but before generating the code,  *)
(* we still need to unify  *)
(* - jumper's s1 and jumpee's s0 stacks; *)
(* - both s0 stacks on JUMPI branching; *)
(* - both s1 stacks on joins. *)
(* and to check their consistency on forks. *)
