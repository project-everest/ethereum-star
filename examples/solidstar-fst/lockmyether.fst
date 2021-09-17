module LockMyEther

open EtherST
open Solidity

type user = {
	bal: uint;
	expiration_block: uint;
	trickle: bool;
	trickle_block: uint;
}


type storage = {
	owner: ref address;
	fees: mapping address (uint);
	user: mapping address (user);
}

let validStore h s = (
  contains h s.owner
  /\ contains h s.fees
  /\ contains h s.user)

assume val getStorage: unit -> ST storage
  (requires (fun h -> true))
  (ensures (fun h x h' -> h=h' /\ validStore h' x))

let store = getStorage()
let msg = getMessage()
let block = getBlock()


let lockMyEther () : GoodEth unit =
  store.owner := (msg.sender);
    update_map (store.fees) (store.owner) (to_uint 0)

let main () : GoodEth unit =
  let fee : uint = div (msg.value) (to_uint 200) in
    update_map (store.fees) (store.owner) (add (lookup (store.fees) (store.owner)) (fee));
    let deposit : uint = sub (msg.value) (fee) in
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = add ((lookup (store.user) (msg.sender)).bal) (deposit)});
    if (gt ((lookup (store.user) (msg.sender)).expiration_block) (to_uint 0)) then
    ()
  else
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = to_uint 0})

let withdraw () : GoodEth unit =
  if ((eq ((lookup (store.user) (msg.sender)).trickle) (true)) && (gt ((lookup (store.user) (msg.sender)).expiration_block) (block.number))) then
    let balance_per_block : uint = div ((lookup (store.user) (msg.sender)).bal) (sub ((lookup (store.user) (msg.sender)).expiration_block) ((lookup (store.user) (msg.sender)).trickle_block)) in
        let trickle_balance : uint = mul (balance_per_block) (sub (block.number) ((lookup (store.user) (msg.sender)).trickle_block)) in
        send (msg.sender) (trickle_balance);
        update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = sub ((lookup (store.user) (msg.sender)).bal) (trickle_balance)});
        update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle_block = block.number})
  else
    if (gt ((lookup (store.user) (msg.sender)).expiration_block) (block.number)) then
      ()
    else
      send (msg.sender) ((lookup (store.user) (msg.sender)).bal);
            update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = to_uint 0});
            update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = to_uint 0})

let withdrawFees () : GoodEth unit =
  if (eq (msg.sender) (store.owner)) then
    send (store.owner) (lookup (store.fees) (store.owner))
  else
    update_map (store.fees) (store.owner) (to_uint 0)

let getBalance () : GoodEth uint =
  (lookup (store.user) (msg.sender)).bal

let getFeeBalance () : GoodEth uint =
  if (eq (msg.sender) (store.owner)) then
    lookup (store.fees) (store.owner)
  else
    ()

let getLatestBlock () : GoodEth uint =
  block.number

let getExpirationBlock () : GoodEth uint =
  (lookup (store.user) (msg.sender)).expiration_block

let getTrickleBlock () : GoodEth uint =
  (lookup (store.user) (msg.sender)).trickle_block

let getTrickle () : GoodEth bool =
  (lookup (store.user) (msg.sender)).trickle

let setExpirationBlock (_blocknumber:uint) : GoodEth unit =
  if (gt ((lookup (store.user) (msg.sender)).expiration_block) (to_uint 0)) then
    ()
  else
    if (gt (_blocknumber) (add (block.number) (to_uint 9000000))) then
      ()
    else
      update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = _blocknumber})

let setTrickleOn () : GoodEth unit =
  update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle = true});
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle_block = block.number})

let setTrickleOff () : GoodEth unit =
  update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle = false})

let __default () : GoodEth unit =
  main ()

let lockMyEther () : GoodEth unit =
  store.owner := (msg.sender);
    update_map (store.fees) (store.owner) (to_uint 0)

let main () : GoodEth unit =
  let fee : uint = div (msg.value) (to_uint 200) in
    update_map (store.fees) (store.owner) (add (lookup (store.fees) (store.owner)) (fee));
    let deposit : uint = sub (msg.value) (fee) in
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = add ((lookup (store.user) (msg.sender)).bal) (deposit)});
    if (gt ((lookup (store.user) (msg.sender)).expiration_block) (to_uint 0)) then
    ()
  else
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = to_uint 0})

let withdraw () : GoodEth unit =
  if ((eq ((lookup (store.user) (msg.sender)).trickle) (true)) && (gt ((lookup (store.user) (msg.sender)).expiration_block) (block.number))) then
    let balance_per_block : uint = div ((lookup (store.user) (msg.sender)).bal) (sub ((lookup (store.user) (msg.sender)).expiration_block) ((lookup (store.user) (msg.sender)).trickle_block)) in
        let trickle_balance : uint = mul (balance_per_block) (sub (block.number) ((lookup (store.user) (msg.sender)).trickle_block)) in
        send (msg.sender) (trickle_balance);
        update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = sub ((lookup (store.user) (msg.sender)).bal) (trickle_balance)});
        update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle_block = block.number})
  else
    if (gt ((lookup (store.user) (msg.sender)).expiration_block) (block.number)) then
      ()
    else
      send (msg.sender) ((lookup (store.user) (msg.sender)).bal);
            update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with bal = to_uint 0});
            update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = to_uint 0})

let withdrawFees () : GoodEth unit =
  if (eq (msg.sender) (store.owner)) then
    send (store.owner) (lookup (store.fees) (store.owner))
  else
    update_map (store.fees) (store.owner) (to_uint 0)

let getBalance () : GoodEth uint =
  (lookup (store.user) (msg.sender)).bal

let getFeeBalance () : GoodEth uint =
  if (eq (msg.sender) (store.owner)) then
    lookup (store.fees) (store.owner)
  else
    ()

let getLatestBlock () : GoodEth uint =
  block.number

let getExpirationBlock () : GoodEth uint =
  (lookup (store.user) (msg.sender)).expiration_block

let getTrickleBlock () : GoodEth uint =
  (lookup (store.user) (msg.sender)).trickle_block

let getTrickle () : GoodEth bool =
  (lookup (store.user) (msg.sender)).trickle

let setExpirationBlock (_blocknumber:uint) : GoodEth unit =
  if (gt ((lookup (store.user) (msg.sender)).expiration_block) (to_uint 0)) then
    ()
  else
    if (gt (_blocknumber) (add (block.number) (to_uint 9000000))) then
      ()
    else
      update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with expiration_block = _blocknumber})

let setTrickleOn () : GoodEth unit =
  update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle = true});
    update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle_block = block.number})

let setTrickleOff () : GoodEth unit =
  update_map (store.user) (msg.sender) ({lookup (store.user) (msg.sender) with trickle = false})

let __default () : GoodEth unit =
  main ()

