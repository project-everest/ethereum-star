module Runtime

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
    (fun (b:UInt8.t) (n:nat) -> UInt8.v b) w 0

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
