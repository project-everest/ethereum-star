module LockMyEther

open FStar.Heap
open FStar.UInt
open Solidity

type user = {
	balance: uint;
	expiration_block: uint;
	trickle: bool;
	trickle_block: uint;
}



type state = {
	owner: address;
	fees: mapping address (uint);
	user: mapping address (user);
}


let lockMyEther () : unit =
  upd (state.owner) (msg.sender);
    upd_map (state.fees) (state.owner) (0)

let __default () : unit =
  main ()

let main () : unit =
  let fee : uint = div (msg.value) (200) in
    upd_map (state.fees) (state.owner) (add (lookup (state.fees) (state.owner)) (fee));
    let deposit : uint = sub (msg.value) (fee) in
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = add (balance (lookup (state.user) (msg.sender))) (deposit)});
    if (gt ((lookup (state.user) (msg.sender)).expiration_block) (0)) then
    ()
  else
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = 0})

let withdraw () : unit =
  if ((eq ((lookup (state.user) (msg.sender)).trickle) (true)) && (gt ((lookup (state.user) (msg.sender)).expiration_block) (block.number))) then
    let balance_per_block : uint = div (balance (lookup (state.user) (msg.sender))) (sub ((lookup (state.user) (msg.sender)).expiration_block) ((lookup (state.user) (msg.sender)).trickle_block)) in
        let trickle_balance : uint = mul (balance_per_block) (sub (block.number) ((lookup (state.user) (msg.sender)).trickle_block)) in
        send (msg.sender) (trickle_balance);
        upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = sub (balance (lookup (state.user) (msg.sender))) (trickle_balance)});
        upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle_block = block.number})
  else
    if (gt ((lookup (state.user) (msg.sender)).expiration_block) (block.number)) then
      ()
    else
      send (msg.sender) (balance (lookup (state.user) (msg.sender)));
            upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = 0});
            upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = 0})

let withdrawFees () : unit =
  if (eq (msg.sender) (state.owner)) then
    send (state.owner) (lookup (state.fees) (state.owner))
  else
    upd_map (state.fees) (state.owner) (0)

let getBalance () : uint =
  balance (lookup (state.user) (msg.sender))

let getFeeBalance () : uint =
  if (eq (msg.sender) (state.owner)) then
    lookup (state.fees) (state.owner)
  else
    ()

let getLatestBlock () : uint =
  block.number

let getExpirationBlock () : uint =
  (lookup (state.user) (msg.sender)).expiration_block

let getTrickleBlock () : uint =
  (lookup (state.user) (msg.sender)).trickle_block

let getTrickle () : bool =
  (lookup (state.user) (msg.sender)).trickle

let setExpirationBlock (_blocknumber:uint) : unit =
  if (gt ((lookup (state.user) (msg.sender)).expiration_block) (0)) then
    ()
  else
    if (gt (_blocknumber) (add (block.number) (9000000))) then
      ()
    else
      upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = _blocknumber})

let setTrickleOn () : unit =
  upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle = true});
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle_block = block.number})

let setTrickleOff () : unit =
  upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle = false})

let lockMyEther () : unit =
  upd (state.owner) (msg.sender);
    upd_map (state.fees) (state.owner) (0)

let __default () : unit =
  main ()

let main () : unit =
  let fee : uint = div (msg.value) (200) in
    upd_map (state.fees) (state.owner) (add (lookup (state.fees) (state.owner)) (fee));
    let deposit : uint = sub (msg.value) (fee) in
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = add (balance (lookup (state.user) (msg.sender))) (deposit)});
    if (gt ((lookup (state.user) (msg.sender)).expiration_block) (0)) then
    ()
  else
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = 0})

let withdraw () : unit =
  if ((eq ((lookup (state.user) (msg.sender)).trickle) (true)) && (gt ((lookup (state.user) (msg.sender)).expiration_block) (block.number))) then
    let balance_per_block : uint = div (balance (lookup (state.user) (msg.sender))) (sub ((lookup (state.user) (msg.sender)).expiration_block) ((lookup (state.user) (msg.sender)).trickle_block)) in
        let trickle_balance : uint = mul (balance_per_block) (sub (block.number) ((lookup (state.user) (msg.sender)).trickle_block)) in
        send (msg.sender) (trickle_balance);
        upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = sub (balance (lookup (state.user) (msg.sender))) (trickle_balance)});
        upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle_block = block.number})
  else
    if (gt ((lookup (state.user) (msg.sender)).expiration_block) (block.number)) then
      ()
    else
      send (msg.sender) (balance (lookup (state.user) (msg.sender)));
            upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with balance = 0});
            upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = 0})

let withdrawFees () : unit =
  if (eq (msg.sender) (state.owner)) then
    send (state.owner) (lookup (state.fees) (state.owner))
  else
    upd_map (state.fees) (state.owner) (0)

let getBalance () : uint =
  balance (lookup (state.user) (msg.sender))

let getFeeBalance () : uint =
  if (eq (msg.sender) (state.owner)) then
    lookup (state.fees) (state.owner)
  else
    ()

let getLatestBlock () : uint =
  block.number

let getExpirationBlock () : uint =
  (lookup (state.user) (msg.sender)).expiration_block

let getTrickleBlock () : uint =
  (lookup (state.user) (msg.sender)).trickle_block

let getTrickle () : bool =
  (lookup (state.user) (msg.sender)).trickle

let setExpirationBlock (_blocknumber:uint) : unit =
  if (gt ((lookup (state.user) (msg.sender)).expiration_block) (0)) then
    ()
  else
    if (gt (_blocknumber) (add (block.number) (9000000))) then
      ()
    else
      upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with expiration_block = _blocknumber})

let setTrickleOn () : unit =
  upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle = true});
    upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle_block = block.number})

let setTrickleOff () : unit =
  upd_map (state.user) (msg.sender) ({lookup (state.user) (msg.sender) with trickle = false})

