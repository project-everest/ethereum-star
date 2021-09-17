module Test

open FStar.Char
open FStar.List.Tot
open FStar.UInt8
open FStar.Heap
open FStar.Mul

type bytes = list UInt8.t
type word = b:bytes{length b <= 32}

assume val gas: ref nat
assume val mem: r:ref nat{gas <> r}

val burn: n:nat -> ST unit
  (requires (fun h0 -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 gas = sel h0 gas + n /\
    sel h1 mem = sel h0 mem))
let burn n = gas := !gas + n

let max a b = if a < b then b else a

val nat_of_word: w:word -> Tot nat
let nat_of_word w =
  List.Tot.fold_right
    (fun (b:UInt8.t) (n:nat) -> UInt8.to_int b) w 0

let g_zero = 0
let g_base = 2
let g_verylow = 3
let g_low = 5
let g_mid = 8
let g_high = 10
let g_ext = 20
let g_sload = 50
let g_exp = 10
let g_expbyte = 10
let g_copy = 3
let g_jumpdest = 1
let g_log = 375
let g_logdata = 8
let g_memory = 3
let g_sset = 20000
let g_call = 40
let g_callvalue = 9000
let g_callnewaccount = 25000
let g_callstipend = 2300

val cost_memory: a:nat -> Tot nat
let cost_memory a = op_Multiply a g_memory

assume val mstore: addr:word -> v:word -> ST unit
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    let mu_i  = sel h0 mem in
    let mu_i' = sel h1 mem in
    let addr = nat_of_word addr in
    mu_i' = max mu_i ((addr + 32) / 32) /\
    sel h1 gas <= sel h0 gas
		 + g_verylow
		 + cost_memory (mu_i' - mu_i)))

assume val get_calldataload: word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas = g_verylow + sel h0 gas))

assume val sload: word -> ST word
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    sel h1 gas = sel h0 gas + g_sload /\
    sel h1 mem = sel h0 mem))

assume val sstore: word -> word -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    sel h1 gas <= sel h0 gas + g_sset /\
    sel h1 mem = sel h0 mem))

assume val loadLocal: word -> word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas = sel h0 gas))

assume val pow: base:word -> exp:word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    (let g1 = sel h1 gas in
     let g0 = sel h0 gas in
     let c = length exp * 8 in // floor (log_256 exp)
     if nat_of_word exp > 0 then
       g1 <= g0 + g_exp + g_expbyte * (1 + c)
     else
       g1 = g0)))

assume val div: a:word -> b:word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas = g_low + sel h0 gas))

assume val add: a:word -> b:word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas = g_verylow + sel h0 gas))

assume val eqw: a:word -> b:word -> ST word
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas = g_verylow + sel h0 gas))

assume val call:target:word -> inGas:word -> inValue:word->inputs:word -> ST (tuple2 (option word) word)
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
    sel h1 mem = sel h0 mem /\
    sel h1 gas <= g_call + g_callvalue + g_callnewaccount + sel h0 gas))

assume val nonZero: word -> Tot bool

assume val get_caller: unit -> Tot word

assume val sub: word -> word -> Tot word

assume val land: word -> word -> Tot word

assume val sha3: word -> word -> Tot word

assume val localStore: word -> word -> word -> Tot unit

assume val get_callvalue: unit -> Tot word

let one:word = [0x01uy]

let zero:word = [0x00uy]

#set-options "--z3timeout 30"

val contract: unit -> ST word
  (requires (fun h -> sel h mem = 0 /\ sel h gas = 0))
  (ensures  (fun h0 _ h1 ->
    sel h1 gas <= 75000))

let contract () =
  burn 6 (* opcodes: PUSH1 60, PUSH1 40 *);
  mstore [0x40uy] [0x60uy];
  burn 6 (* opcodes: PUSH1 E0, PUSH1 02 *);
  let x_1 = pow [0x02uy] [0xE0uy] in
  burn 3 (* opcodes: PUSH1 00 *);
  let x_2 = get_calldataload [0x00uy] in
  let x_3 = div x_2 x_1 in
  let x_4 = eqw x_3 [0x57uy; 0xEAuy; 0x89uy; 0xB6uy] in
  burn 10 (* opcode JUMPI *);
  let h = ST.get() in
  assert (sel h gas < 1000);
  if nonZero x_4 then
    begin (* offset: 46 *)
    burn 13 (* opcodes: JUMPDEST, PUSH1 2C, PUSH1 01, PUSH1 A0, PUSH1 02 *);
    let x_5 = pow [0x02uy] [0xA0uy] in
    let x_6 = sub x_5 [0x01uy] in
    let x_7 = get_caller () in
    let x_8 = land x_7 x_6 in
    burn 17 (* opcodes: SUB, CALLER, AND, PUSH1 00, DUP2, DUP2 *);
    mstore [0x00uy] x_8;
    burn 9 (* opcodes: PUSH1 20, DUP2, SWAP1 *);
    mstore [0x20uy] [0x00uy];
    burn 6 (* opcodes: PUSH1 40, DUP2 *);
    let x_9 = sha3 [0x00uy] [0x40uy] in
    let x_10 = sload x_9 in
    burn 24 (* opcodes: PUSH1 60, DUP3, DUP2, DUP2, DUP2, DUP6, DUP9, DUP4 *);
    let inputs = loadLocal [0x60uy] [0x00uy] in
    let h = ST.get() in
    cut (sel h gas < 10000);
    let (result,gasLeft) = call x_8 [0x00uy] x_10 inputs in
    let x_11 =
      match result with
      | Some outputs ->
	begin
	localStore [0x60uy] [0x00uy] outputs;
	one
	end
      | None -> zero
    in
    let x_12 = get_caller () in
    burn 38 (* opcodes: SWAP4, POP, POP, POP, POP, POP, PUSH1 00, PUSH1 00, PUSH1 00, POP, PUSH1 00, CALLER, PUSH1 01, PUSH1 A0, PUSH1 02 *);
    let x_13 = pow [0x02uy] [0xA0uy] in
    let x_14 = sub x_13 [0x01uy] in
    let x_15 = land x_14 x_12 in
    burn 9 (* opcodes: SUB, AND, DUP2 *);
    mstore [0x00uy] x_15;
    let x_16 = add [0x20uy] [0x00uy] in
    burn 12 (* opcodes: PUSH1 20, ADD, SWAP1, DUP2 *);
    mstore [0x20uy] [0x00uy];
    let x_17 = add [0x20uy] x_16 in
    burn 9 (* opcodes: PUSH1 20, ADD, PUSH1 00 *);
    let x_18 = sha3 [0x00uy] x_17 in
    burn 11 (* opcodes: PUSH1 00, POP, DUP2, SWAP1 *);
    sstore x_18 [0x00uy];
    burn 8 (* opcode JUMP *);
    (*  burn 0 (* opcode STOP *) *)
     [] (* no returned outputs *)
    end
  else
    begin (* offset: 24 *)
    let x_19 = eqw [0xEDuy; 0x21uy; 0x24uy; 0x8Cuy] x_3 in
    burn 10 (* opcode JUMPI *);
    if nonZero x_19 then
      begin (* offset: 131 *)
      burn 13 (* opcodes: JUMPDEST, PUSH1 2C, PUSH1 01, PUSH1 A0, PUSH1 02 *);
      let x_20 = pow [0x02uy] [0xA0uy] in
      let x_21 = sub x_20 [0x01uy] in
      let x_22 = get_caller () in
      let x_23 = land x_22 x_21 in
      burn 17 (* opcodes: SUB, CALLER, AND, PUSH1 00, SWAP1, DUP2 *);
      mstore [0x00uy] x_23;
      burn 9 (* opcodes: PUSH1 20, DUP2, SWAP1 *);
      mstore [0x20uy] [0x00uy];
      burn 6 (* opcodes: PUSH1 40, SWAP1 *);
      let x_24 = sha3 [0x00uy] [0x40uy] in
      burn 3 (* opcodes: DUP1 *);
      let x_25 = sload x_24 in
      let x_26 = get_callvalue () in
      let x_27 = add x_26 x_25 in
      burn 8 (* opcodes: CALLVALUE, ADD, SWAP1 *);
      sstore x_24 x_27;
      burn 8 (* opcode JUMP *);
       [] (* no returned outputs *)
      end
    else
      begin (* offset: 34 *)
      let x_28 = eqw [0xF8uy; 0xF8uy; 0xA9uy; 0x12uy] x_3 in
      burn 10 (* opcode JUMPI *);
      if nonZero x_28 then
        begin (* offset: 165 *)
        burn 10 (* opcodes: JUMPDEST, PUSH1 01, PUSH1 A0, PUSH1 02 *);
        let x_29 = pow [0x02uy] [0xA0uy] in
        let x_30 = sub x_29 [0x01uy] in
        let x_31 = get_caller () in
        let x_32 = land x_31 x_30 in
        burn 17 (* opcodes: SUB, CALLER, AND, PUSH1 00, SWAP1, DUP2 *);
        mstore [0x00uy] x_32;
        burn 9 (* opcodes: PUSH1 20, DUP2, DUP2 *);
        mstore [0x20uy] [0x00uy];
        burn 9 (* opcodes: PUSH1 40, SWAP1, SWAP2 *);
        let x_33 = sha3 [0x00uy] [0x40uy] in
        let x_34 = sload x_33 in
        burn 9 (* opcodes: PUSH1 60, SWAP1, DUP2 *);
        mstore [0x60uy] x_34;
        loadLocal [0x60uy] [0x20uy] (* returned outputs *)
        end
      else
        begin (* offset: 44 *)
         [] (* no returned outputs *)
        end
      end
  end
