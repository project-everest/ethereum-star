module Solidity

open FStar.ST
open FStar.UInt
open FStar.Heap

type uint = uint_t 256

val to_uint: int -> Tot uint
let to_uint n = to_uint_t 256 n 
assume val div: uint -> uint -> Tot uint
(* let div a b = if (b = zero 256) then zero 256 else  div a b *)
assume val mul: uint -> uint -> Tot uint
assume val add: uint -> uint -> Tot uint
assume val sub: uint -> uint -> Tot uint
assume val gt: uint -> uint -> Tot bool
assume val eq: uint -> uint -> Tot bool
assume val lt: uint -> uint -> Tot bool
assume val leq: uint -> uint -> Tot bool
assume val geq: uint -> uint -> Tot bool

type address = uint_t 256

type mapping (key:eqtype) (value:Type) = ref (FStar.Map.t key value)

val lookup: #key:eqtype -> #value:Type -> m:mapping key value -> key
         -> ST value
  (requires (fun h -> contains h m))
  (ensures (fun h x h' -> h == h'))
let lookup #key #value m k = FStar.Map.sel (read m) k

val update_map: #key:eqtype -> #value:Type
  -> m:mapping key value
  -> key -> value
  -> ST unit
  (requires (fun h -> contains h m))
  (ensures (fun h0 x h1 -> modifies (only m) h0 h1))

let update_map #key #value m k v =
  let map = read m in
  write m (FStar.Map.upd map k v)

type msg = {
     value : uint;
     sender: address;
}

assume val getMessage: unit -> ST msg
       (requires (fun h -> true))
       (ensures (fun h x h' -> h == h'))

type block = {
     number : uint;
}

assume val getBlock: unit -> ST block
       (requires (fun h -> true))
       (ensures (fun h x h' -> h == h'))
