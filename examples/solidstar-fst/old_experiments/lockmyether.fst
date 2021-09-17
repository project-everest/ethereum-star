module LockMyEther

open EtherST
open Solidity

type user = {
	balance: uint;
	expiration_block: uint;
	trickle: bool;
	trickle_block: uint;
}

type storage = {
	owner: ref address;
	fees: mapping address (uint);
	users: mapping address (user);
}

let validStore h s = 
    (contains h s.owner /\ 
     contains h s.fees /\ 
     contains h s.users )

assume val getStorage: unit -> ST storage
       (requires (fun h -> true))
       (ensures (fun h x h' -> h==h' /\ 
       		               validStore h' x))

let store = getStorage()
let msg = getMessage()
let block = getBlock()

val lockMyEther: unit -> ST unit
       (requires (fun h -> validStore h store))
       (ensures (fun h x h' -> validStore h' store))
let lockMyEther () =
    store.owner := msg.sender;
    upd store.fees !store.owner 0

val main: unit -> ST unit
       (requires (fun h -> validStore h store))
       (ensures (fun h x h' -> validStore h' store))
let main () =
    let owner = !(store.owner) in
    let fee : uint = div msg.value (to_uint 200) in
    let nfee : uint =  add (sel store.fees owner) fee in
    upd store.fees owner nfee;
    let deposit : uint = sub msg.value fee in
    let user = sel store.users msg.sender in
    let user = {user with balance = add user.balance deposit} in
    upd store.users msg.sender user; 
    let user = sel store.users msg.sender in
    if (gt user.expiration_block 0) then
       ()
    else 
        let user = sel store.users msg.sender in
        let user = {user with expiration_block = 0} in
    	upd store.users msg.sender user

val withdraw: unit -> ST unit
       (requires (fun h -> validStore h store))
       (ensures (fun h x h' -> validStore h' store))
let withdraw () =
    let user = sel store.users msg.sender in
    if ((user.trickle = true) && 
        (gt user.expiration_block block.number)) then
	let balance_per_block : uint = div  user.balance (sub user.expiration_block user.trickle_block) in
	let trickle_balance : uint = mul balance_per_block (sub block.number user.trickle_block) in
	let _ = send msg.sender trickle_balance in
	let user = sel store.users msg.sender in
	let user = {user with 
	    	    balance = sub user.balance trickle_balance;
		    trickle_block = block.number} in
    	upd store.users msg.sender user
    else
    if (gt user.expiration_block block.number) then ()
    else 
	let _ = send msg.sender user.balance in
	let user = sel store.users msg.sender in
	let user = {user with 
	    	    balance = 0;
		    expiration_block = 0} in
    	upd store.users msg.sender user
       

(*
let withdrawFees () : unit =
if ((msg.sender = owner)) then
(owner.send) (fees[owner])
;
fees[owner] = 0
let getBalance () : uint =
raise Return(user[msg.sender].balance)
let getFeeBalance () : uint =
if ((msg.sender = owner)) then
raise Return(fees[owner])

let getLatestBlock () : uint =
raise Return(block.number)
let getExpirationBlock () : uint =
raise Return(user[msg.sender].expiration_block)
let getTrickleBlock () : uint =
raise Return(user[msg.sender].trickle_block)
let getTrickle () : bool =
raise Return(user[msg.sender].trickle)
let setExpirationBlock (_blocknumber:uint) : unit =
if ((user[msg.sender].expiration_block > 0)) then
raise Return()
;
if ((_blocknumber > (block.number + 9000000))) then
raise Return()
;
user[msg.sender].expiration_block = _blocknumber
let setTrickleOn () : unit =
user[msg.sender].trickle = true;
user[msg.sender].trickle_block = block.number
let setTrickleOff () : unit =
user[msg.sender].trickle = false
let lockMyEther () : unit =
owner = msg.sender;
fees[owner] = 0
let __default () : unit =
(main) 
let main () : unit =
let fee : uint = (match 200 with | 0 -> 0 | n -> msg.value / n) in
;
fees[owner] = (fees[owner] + fee);
let deposit : uint = (msg.value - fee) in
;
user[msg.sender].balance = (user[msg.sender].balance + deposit);
if ((user[msg.sender].expiration_block > 0)) then
raise Return()
;
user[msg.sender].expiration_block = 0
let withdraw () : unit =
if (((user[msg.sender].trickle = true) && (user[msg.sender].expiration_block > block.number))) then
let balance_per_block : uint = (match (user[msg.sender].expiration_block - user[msg.sender].trickle_block) with | 0 -> 0 | n -> user[msg.sender].balance / n) in
;
let trickle_balance : uint = (op_Multiply balance_per_block (block.number - user[msg.sender].trickle_block)) in
;
(msg.sender.send) (trickle_balance);
user[msg.sender].balance = (user[msg.sender].balance - trickle_balance);
user[msg.sender].trickle_block = block.number
else
if ((user[msg.sender].expiration_block > block.number)) then
raise Return()
;
(msg.sender.send) (user[msg.sender].balance);
user[msg.sender].balance = 0;
user[msg.sender].expiration_block = 0
let withdrawFees () : unit =
if ((msg.sender = owner)) then
(owner.send) (fees[owner])
;
fees[owner] = 0
let getBalance () : uint =
raise Return(user[msg.sender].balance)
let getFeeBalance () : uint =
if ((msg.sender = owner)) then
raise Return(fees[owner])

let getLatestBlock () : uint =
raise Return(block.number)
let getExpirationBlock () : uint =
raise Return(user[msg.sender].expiration_block)
let getTrickleBlock () : uint =
raise Return(user[msg.sender].trickle_block)
let getTrickle () : bool =
raise Return(user[msg.sender].trickle)
let setExpirationBlock (_blocknumber:uint) : unit =
if ((user[msg.sender].expiration_block > 0)) then
raise Return()
;
if ((_blocknumber > (block.number + 9000000))) then
raise Return()
;
user[msg.sender].expiration_block = _blocknumber
let setTrickleOn () : unit =
user[msg.sender].trickle = true;
user[msg.sender].trickle_block = block.number
let setTrickleOff () : unit =
user[msg.sender].trickle = false
let handler (m:msg) =
*)
