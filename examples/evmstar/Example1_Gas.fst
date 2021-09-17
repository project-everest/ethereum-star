module Example1_Gas

open FStar.Heap
open Runtime

val contract: unit -> ST word
  (requires (fun h -> sel h gas = 0 /\ sel h mem = 0))
  (ensures  (fun h0 _ h1 -> sel h1 gas <= 20241))

let contract() =
  burn 6 (* opcodes: PUSH1 60, NOP, PUSH1 40, NOP *);
  mstore [0x40uy] [0x60uy]; //12
  burn 6 (* opcodes: PUSH1 E0, NOP, PUSH1 02, NOP *);
  let x_1 = pow [0x02uy] [0xE0uy] in //100
  burn 3 (* opcodes: PUSH1 00, NOP *);
  let x_2 = get_calldataload [0x00uy] in //3
  let x_3 = div x_2 x_1 in //5
  let x_4 = eqw x_3 [0x41uy; 0x7Duy; 0xEFuy; 0x24uy] in //3
  burn 10 (* opcode JUMPI *);
  let h = ST.get () in assert (sel h gas <= 148);
  if nonZero x_4 then
    begin (* offset: 26 *)
    burn 7 (* opcodes: JUMPDEST, PUSH1 00, NOP, DUP1 *);
    let x_5 = sload [0x00uy] in //50
    burn 3 (* opcodes: PUSH1 04, NOP *);
    let x_6 = get_calldataload [0x04uy] in //3
    let x_7 = add x_6 x_5 in //3
    burn 12 (* opcodes: ADD, SWAP1, DUP2, SWAP1 *);
    sstore [0x00uy] x_7; //<=20000
    burn 9 (* opcodes: PUSH1 60, NOP, SWAP1, DUP2 *);
    mstore [0x60uy] x_7; //6
    (*  burn 0 (* opcode RETURN *) *)
    loadLocal [0x60uy] [0x20uy] (* returned outputs *)
    end
  else
    begin (* offset: 24 *)
     (*  burn 0 (* opcode STOP *) *)
     [] (* no returned outputs *)
    end
