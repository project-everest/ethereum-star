module Tezos.Interpreter

open FStar.Tactics

open Tezos.Primitives
open Tezos.Definitions
open Tezos.UntypedDefinitions
open Tezos.Definitions
open Tezos.Storage
open Tezos.Error
open Tezos.AbstractInterpreter
open Tezos.Serialization

module Script = Tezos.ScriptRepr
module CI = CryptoInterface
module F = FStar_interface


val move_refinement: #a:Type -> #p:(a -> Type)
  -> l:list a{forall z. List.Tot.memP z l ==> p z} -> list (x:a{p x})
let rec move_refinement #a #p = function
  | [] -> []
  | hd :: tl -> hd :: move_refinement #a #p tl

val forall_memP_precedes: #a:Type -> l:list a -> Lemma (forall x. List.Tot.memP x l ==> x << l)
let forall_memP_precedes #a l =
  let open FStar.Tactics in
  let open FStar.List.Tot in
  assert_by_tactic (forall x. memP x l ==> x << l)
    (x <-- forall_intro; mapply (quote memP_precedes))

val aux: #a:Type -> #b:Type -> l:list a -> m:b{l << m} -> list (x:a{x << m})
let aux #a #b l m = forall_memP_precedes l; move_refinement l


(** Untyped stack with tagged data items *)
type stack =
  | Item  : top:tagged_data -> rest:stack -> stack
  | Empty : stack

val string_of_stack : stack -> string

let rec string_of_stack = function
| Empty -> "[]"
| Item top rest -> (tagged_data_to_string top) ^ " : " ^ (string_of_stack rest)

unfold type quota = nat

type origination_nonce =
  { operation_hash: contract_hash;
    origination_index: int }

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 50"

val interp:
  origination:origination_nonce ->
  qta:quota ->
  orig:contract ->
  source:contract ->
  amount:tez ->
  ctxt:context ->
  code:uinstr ->
  arg:tagged_data ->
  Tot (tzresult (tagged_data * (qta':quota{qta' <= qta}) * context * origination_nonce))
  (decreases %[qta; code; 1])

val step:
  origination:origination_nonce ->
  qta:quota ->
  orig:contract ->
  source:contract ->
  amount:tez ->
  ctxt:context ->
  code:uinstr ->
  st:stack ->
  Tot (tzresult (stack * (qta':quota{qta' <= qta}) * context * origination_nonce))
  (decreases %[qta; code; 0])

// val execute:
//   origination_nonce ->
//   contract -> contract -> context ->
//   Script.storage -> Script.code -> tez ->
//   Script.expr -> int ->
//   tzresult (Script.expr * Script.expr * int * context * origination_nonce)

/// code to build expressions accepted by FStar_interface
val make_expr : (e : Script.expr) -> Tot Script.expr (decreases e)
val make_list_expr : (l : list Script.expr) -> Tot (list Script.expr) (decreases l)

// let rec make_expr (e : Script.expr) = match e with
//   | Script.Int s -> F.make_int s
//   | Script.String s -> F.make_string s
//   | Script.Prim s l -> F.make_prim s (make_list_expr l)
//   | Script.Seq l -> F.make_seq (make_list_expr l)
// and make_list_expr l = match l with
// | [] -> []
// | x::xs -> (make_expr x) :: make_list_expr xs


(**
  * The OCaml code uses [int] for [qta] and checks if [qta <= 0]
  * We need to use [nat] because we use it as a termination argument
  * REMARK: While the OCaml code can return [-1], we always return a [nat]
  *)
let rec step origination qta orig source amount ctxt ui st =
  let logged_return (ret, qta, ctxt) = return (ret, qta, ctxt, origination) in
  match qta with
  | 0 -> fail Quota_exceeded
  | _ ->
    begin
    match ui, st with
    | Drop, Item _ rest ->
      logged_return (rest, qta - 1, ctxt)

    | Dup, Item v rest ->
      logged_return (Item v (Item v rest), qta - 1, ctxt)

    | Swap, Item vi (Item vo rest) ->
      logged_return (Item vo (Item vi rest), qta - 1, ctxt)

    (* The following Const_* replace the generic: *)
    // | Const v, rest ->
    //   logged_return (Item (v, rest), qta - 1, ctxt)

    | Const_bool v, rest ->
      logged_return (Item (DBool v) rest, qta - 1, ctxt)

    | Const_unit, rest ->
      logged_return (Item (DUnit) rest, qta - 1, ctxt)

    | Const_int v, rest ->
      logged_return (Item (DInt v) rest, qta - 1, ctxt)

    | Const_nat v, rest ->
      logged_return (Item (Nat v) rest, qta - 1, ctxt)

    | Const_tez v, rest ->
      logged_return (Item (DTez v) rest, qta - 1, ctxt)

    | Const_string v, rest ->
      logged_return (Item (DString v) rest, qta - 1, ctxt)

    (* options *)
    | Cons_some, Item v rest ->
      logged_return (Item (DOption (Some v)) rest, qta - 1, ctxt)

    | Cons_none _, rest ->
      logged_return (Item (DOption None) rest, qta - 1, ctxt)

    | If_none bt _, Item (DOption None) rest ->
      step origination qta orig source amount ctxt bt rest

    | If_none _ bf, Item (DOption (Some v)) rest ->
      step origination qta orig source amount ctxt bf (Item v rest)

    (* pairs *)
    | Cons_pair, Item a (Item b rest) ->
      logged_return (Item (DPair a b) rest, qta - 1, ctxt)

    | Car, Item (DPair a _) rest ->
      logged_return (Item a rest, qta - 1, ctxt)

    | Cdr, Item (DPair _ b) rest ->
      logged_return (Item b rest, qta - 1, ctxt)

    (* unions *)
    | Left, Item v rest ->
      logged_return (Item (DUnion (L v)) rest, qta - 1, ctxt)

    | Right, Item v rest ->
      logged_return (Item (DUnion (R v)) rest, qta - 1, ctxt)

    | If_left bt _, Item (DUnion (L v)) rest ->
      step origination qta orig source amount ctxt bt (Item v rest)

    | If_left _ bf, Item (DUnion (R v)) rest ->
      step origination qta orig source amount ctxt bf (Item v rest)

    (* lists *)
    | Cons_list, Item hd (Item (DList tl) rest) ->
      logged_return (Item (DList (hd :: tl)) rest, qta - 1, ctxt)

    | Nill _, rest ->
      logged_return (Item (DList []) rest, qta - 1, ctxt)

    | If_cons _ bf, Item (DList []) rest ->
      step origination qta orig source amount ctxt bf rest

    | If_cons bt _, Item (DList (hd :: tl)) rest ->
      step origination qta orig source amount ctxt bt (Item hd (Item (DList tl) rest))

    | Seq hd tl, st ->
      begin
      res <-- step origination qta orig source amount ctxt hd st;
      let (trans, qta, ctxt, origination) = res in
      res <-- step origination qta orig source amount ctxt tl trans;
      let (trans, qta, ctxt, origination) = res in
      logged_return (trans, qta, ctxt)
      end

    | List_map, Item (DLambda (Lam _ _ lam _)) (Item (DList l) rest) ->
      begin
      (* We deviate from OCaml and start from [qta - 1] to guarantee termination *)
      res <-- List.Tot.fold_right #_  #(tzresult (_ * q:quota{q < qta} * _ * _))
	      (fun arg acc ->
		 acc <-- acc;
		 let (tail, qta', ctxt, origination) = acc in
		 res <-- interp origination qta' orig source amount ctxt lam arg;
		 let (ret, qta'', ctxt, origination) = res in
		 return (ret :: tail, (qta''<:q:quota{q < qta}), ctxt, origination))
	      l
	      (Ok ([], qta - 1, ctxt, origination));
      let (ret, qta', ctxt, origination) = res in
      return (Item (DList ret) rest, (qta'<:q:quota{q <= qta}), ctxt, origination)
      end

    | List_reduce, Item (DLambda (Lam _ _ lam _)) (Item (DList l) (Item init rest)) ->
      begin
      res <-- List.Tot.fold_left #(tzresult (_ * q:quota{q < qta} * _ * _)) #tagged_data
	  (fun acc arg ->
	     acc <-- acc;
	     let (partial, qta', ctxt, origination) = acc in
	     res <-- interp origination qta' orig source amount ctxt lam (DPair arg partial);
	     let (partial, qta'', ctxt, origination) = res in
	     return (partial, (qta''<:q:quota{q < qta}), ctxt, origination))
	  (Ok (init, qta - 1, ctxt, origination))
	  l;
       let (ret, qta', ctxt, origination) = res in
       return (Item ret rest, (qta'<:q:quota{q <= qta}), ctxt, origination)
       end
(*
    (* sets *)
    | Empty_set t, rest ->
      logged_return (Item (DSet (empty_set t)) rest, qta - 1, ctxt)

    | Set_map t, Item (lam, Item (set, rest)) ->
      let items = List.rev (set_fold (fun e acc -> e :: acc) set []) in
      fold_left_s
	(fun (res, qta, ctxt, origination) arg ->
	   interp ?log origination qta orig source amount ctxt lam arg >>=?
	   fun (ret, qta, ctxt, origination) ->
	   return (set_update ret true res, qta, ctxt, origination))
	(empty_set t, qta, ctxt, origination) items >>=? fun (res, qta, ctxt, origination) ->
      logged_return ~origination (Item (res, rest), qta, ctxt)

    | Set_reduce, Item (lam, Item (set, Item (init, rest))) ->
      let items =
	List.rev (set_fold (fun e acc -> e :: acc) set []) in
      fold_left_s
	(fun (partial, qta, ctxt, origination) arg ->
	   interp ?log origination qta orig source amount ctxt lam (arg, partial)
	   >>=? fun (partial, qta, ctxt, origination) ->
	   return (partial, qta, ctxt, origination))
	(init, qta, ctxt, origination) items >>=? fun (res, qta, ctxt, origination) ->
      logged_return ~origination (Item (res, rest), qta, ctxt)

    | Set_mem, Item (v, Item (set, rest)) ->
      logged_return (Item (set_mem v set, rest), qta - 1, ctxt)

    | Set_update, Item (v, Item (presence, Item (set, rest))) ->
      logged_return (Item (set_update v presence set, rest), qta - 1, ctxt)

    | Set_size, Item (set, rest) ->
      logged_return (Item (set_size set, rest), qta - 1, ctxt)

    (* maps *)
    | Empty_map (t, _), rest ->
      logged_return (Item (empty_map t, rest), qta - 1, ctxt)

    | Map_map, Item (lam, Item (map, rest)) ->
      let items =
	List.rev (map_fold (fun k v acc -> (k, v) :: acc) map []) in
      fold_left_s
	(fun (acc, qta, ctxt, origination) (k, v) ->
	   interp ?log origination qta orig source amount ctxt lam (k, v)
	   >>=? fun (ret, qta, ctxt, origination) ->
	   return (map_update k (Some ret) acc, qta, ctxt, origination))
	(empty_map (map_key_ty map), qta, ctxt, origination) items >>=? fun (res, qta, ctxt, origination) ->
      logged_return ~origination (Item (res, rest), qta, ctxt)

    | Map_reduce, Item (lam, Item (map, Item (init, rest))) ->
      let items =
	List.rev (map_fold (fun k v acc -> (k, v) :: acc) map []) in
      fold_left_s
	(fun (partial, qta, ctxt, origination) arg ->
	   interp ?log origination qta orig source amount ctxt lam (arg, partial)
	   >>=? fun (partial, qta, ctxt, origination) ->
	   return (partial, qta, ctxt, origination))
	(init, qta, ctxt, origination) items >>=? fun (res, qta, ctxt, origination) ->
      logged_return ~origination (Item (res, rest), qta, ctxt)

    | Map_mem, Item (v, Item (map, rest)) ->
      logged_return (Item (map_mem v map, rest), qta - 1, ctxt)

    | Map_get, Item (v, Item (map, rest)) ->
      logged_return (Item (map_get v map, rest), qta - 1, ctxt)

    | Map_update, Item (k, Item (v, Item (map, rest))) ->
      logged_return (Item (map_update k v map, rest), qta - 1, ctxt)

    | Map_size, Item (map, rest) ->
      logged_return (Item (map_size map, rest), qta - 1, ctxt)

    (* timestamp operations *)
    | Add_seconds_to_timestamp, Item (n, Item (t, rest)) ->
      begin match Script_int.to_int64 n with
	| None -> fail (Overflow loc)
	| Some n ->
	    Lwt.return
	      (Period.of_seconds n >>? fun p ->
	       Timestamp.(t +? p) >>? fun res ->
	       Ok (Item (res, rest), qta - 1, ctxt)) >>=? fun res ->
	    logged_return res
      end

    | Add_timestamp_to_seconds, Item (t, Item (n, rest)) ->
      begin match Script_int.to_int64 n with
	| None -> fail (Overflow loc)
	| Some n ->
	    Lwt.return
	      (Period.of_seconds n >>? fun p ->
	       Timestamp.(t +? p) >>? fun res ->
	       Ok (Item (res, rest), qta - 1, ctxt)) >>=? fun res ->
	    logged_return res
      end
*)
    (* string operations *)
    | Concat, Item (DString x) (Item (DString y) rest) ->
      logged_return (Item (DString (x ^ y)) rest, qta - 1, ctxt)
(*
    (* currency operations *)
    | Add_tez, Item (x, Item (y, rest)) ->
      Lwt.return Tez.(x +? y) >>=? fun res ->
      logged_return (Item (res, rest), qta - 1, ctxt)

    | Sub_tez, Item (x, Item (y, rest)) ->
      Lwt.return Tez.(x -? y) >>=? fun res ->
      logged_return (Item (res, rest), qta - 1, ctxt)

    | Mul_teznat, Item (x, Item (y, rest)) ->
      begin
      match Script_int.to_int64 y with
      | None -> fail (Overflow loc)
      | Some y ->
	Lwt.return Tez.(x *? y) >>=? fun res ->
	logged_return (Item (res, rest), qta - 1, ctxt)
      end

    | Mul_nattez, Item (y, Item (x, rest)) ->
     begin
       match Script_int.to_int64 y with
       | None -> fail (Overflow loc)
       | Some y ->
	  Lwt.return Tez.(x *? y) >>=? fun res ->
	  logged_return (Item (res, rest), qta - 1, ctxt)
     end
 *)

    (* boolean operations *)
    | Or, Item (DBool x) (Item (DBool y) rest) ->
      logged_return (Item (DBool (x || y)) rest, qta - 1, ctxt)

    | And, Item (DBool x) (Item (DBool y) rest) ->
      logged_return (Item (DBool (x && y)) rest, qta - 1, ctxt)

    | Xor, Item (DBool x) (Item (DBool y) rest) ->
      logged_return (Item (DBool ((not x && y) || (x && not y))) rest, qta - 1, ctxt)

    | Not, Item (DBool x) rest ->
      logged_return (Item (DBool (not x)) rest, qta - 1, ctxt)

    (* integer operations *)
    | Abs_int, Item (DInt x) rest ->
      logged_return (Item (Nat (abs x)) rest, qta - 1, ctxt)

    | Int_nat, Item (Nat x) rest ->
      logged_return (Item (DInt x) rest, qta - 1, ctxt)

    | Neg_int, Item (DInt x) rest ->
      logged_return (Item (DInt (- x)) rest, qta - 1, ctxt)

    | Neg_nat, Item (Nat x) rest ->
      logged_return (Item (DInt (- x)) rest, qta - 1, ctxt)

    | Add_intint, Item (DInt x) (Item (DInt y) rest) ->
      logged_return (Item (DInt (x + y)) rest, qta - 1, ctxt)

    | Add_intnat, Item (DInt x) (Item (Nat y) rest) ->
      logged_return (Item (DInt (x + y)) rest, qta - 1, ctxt)

    | Add_natint, Item (Nat x) (Item (DInt y) rest) ->
      logged_return (Item (DInt (x + y)) rest, qta - 1, ctxt)

    | Add_natnat, Item (Nat x) (Item (Nat y) rest) ->
      logged_return (Item (Nat (x + y)) rest, qta - 1, ctxt)

    // REMARK: In OCaml, this is parameteric on Nat/Int
    | Sub_int, Item (DInt x) (Item (DInt y) rest) ->
      logged_return (Item (DInt (x - y)) rest, qta - 1, ctxt)

    | Sub_int, Item (DInt x) (Item (Nat y) rest) ->
      logged_return (Item (DInt (x - y)) rest, qta - 1, ctxt)

    | Sub_int, Item (Nat x) (Item (DInt y) rest) ->
      logged_return (Item (DInt (x - y)) rest, qta - 1, ctxt)

    | Sub_int, Item (Nat x) (Item (Nat y) rest) ->
      logged_return (Item (DInt (x - y)) rest, qta - 1, ctxt)

    | Mul_intint, Item (DInt x) (Item (DInt y) rest) ->
      let open FStar.Mul in
      logged_return (Item (DInt (x * y)) rest, qta - 1, ctxt)

    | Mul_intnat, Item (DInt x) (Item (Nat y) rest) ->
      let open FStar.Mul in
      logged_return (Item (DInt (x * y)) rest, qta - 1, ctxt)

    | Mul_natint, Item (Nat x) (Item (DInt y) rest) ->
      let open FStar.Mul in
      logged_return (Item (DInt (x * y)) rest, qta - 1, ctxt)

    | Mul_natnat, Item (Nat x) (Item (Nat y) rest) ->
      let open FStar.Mul in
      logged_return (Item (Nat (x * y)) rest, qta - 1, ctxt)

    | Ediv_teznat, Item (DTez x) (Item (Nat y) rest) ->
      fail (Unimplemented "Ediv_teznat")
    (*
      let x = Script_int.of_int64 (Tez.to_cents x) in
      let result =
	match Script_int.ediv x y with
	| None -> None
	| Some (q, r) ->
	   match Script_int.to_int64 q,
		 Script_int.to_int64 r with
	   | Some q, Some r ->
	      begin
		match Tez.of_cents q, Tez.of_cents r with
		| Some q, Some r -> Some (q,r)
		(* Cannot overflow *)
		| _ -> assert False
	      end
	   (* Cannot overflow *)
	   | _ -> assert False
       in
       logged_return (Item (DPair (result, rest)), qta -1, ctxt)
    *)

    | Ediv_tez, Item (DTez x) (Item (DTez y) rest) ->
      fail (Unimplemented "Ediv_tez")
    (*
      let x = Script_int.abs (Script_int.of_int64 (Tez.to_cents x)) in
      let y = Script_int.abs (Script_int.of_int64 (Tez.to_cents y)) in
      begin
	match Script_int.ediv_n x y with
	| None ->
	    logged_return (Item (None, rest), qta -1, ctxt)
	| Some (q, r) ->
	    let r =
	      match Script_int.to_int64 r with
	      | None -> assert False (* Cannot overflow *)
	      | Some r ->
		  match Tez.of_cents r with
		  | None -> assert False (* Cannot overflow *)
		  | Some r -> r in
	    logged_return (Item (Some (q, r), rest), qta -1, ctxt)
      end
    *)

    | Ediv_intint, Item (DInt x) (Item (DInt y) rest) ->
      fail (Unimplemented "Ediv_intint")
      (*
      logged_return (Item (DPair (ediv x y)) rest, qta -1, ctxt)
      *)

    | Ediv_intnat, Item (DInt x) (Item (Nat y) rest) ->
      fail (Unimplemented "Ediv_intnat")
      (*
      logged_return (Item (Script_int.ediv x y, rest), qta -1, ctxt)
      *)

    | Ediv_natint, Item (Nat x) (Item (DInt y) rest) ->
      fail (Unimplemented "Ediv_natint")
      (*
      logged_return (Item (Script_int.ediv x y, rest), qta -1, ctxt)
      *)

    | Ediv_natnat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "Ediv_natnat")
      (*
      logged_return (Item (Script_int.ediv_n x y, rest), qta -1, ctxt)
      *)

    | Lsl_nat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "Lsl_nat")
      (*
      begin match Script_int.shift_left_n x y with
	| None -> fail (Overflow loc)
	| Some r -> logged_return (Item (r, rest), qta - 1, ctxt)
      end
      *)

    | Lsr_nat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "Lsr_nat")
      (*
      begin match Script_int.shift_right_n x y with
	| None -> fail (Overflow loc)
	| Some r -> logged_return (Item (r, rest), qta - 1, ctxt)

      end
      *)

    | Or_nat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "Or_nat")
      (*
      logged_return (Item (Script_int.logor x y, rest), qta - 1, ctxt)
      *)

    | And_nat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "And_nat")
      (*
      logged_return (Item (Script_int.logand x y, rest), qta - 1, ctxt)
      *)

    | Xor_nat, Item (Nat x) (Item (Nat y) rest) ->
      fail (Unimplemented "Xor_nat")
      (*
      logged_return (Item (Script_int.logxor x y, rest), qta - 1, ctxt)
      *)

    | Not_int, Item (DInt x) rest ->
      fail (Unimplemented "Not_int")
      (*
      logged_return (Item (Script_int.lognot x, rest), qta - 1, ctxt)
      *)

    | Not_nat, Item (Nat x) rest ->
      fail (Unimplemented "Not_nat")
      (*
      logged_return (Item (Script_int.lognot x, rest), qta - 1, ctxt)
      *)

    (* control *)
    | Seq hd tl, st ->
      begin
      res <-- step origination qta orig source amount ctxt hd st;
      let (trans, qta', ctxt, origination) = res in
      res <-- step origination qta' orig source amount ctxt tl trans;
      let (ret, qta'', ctxt, origination) = res in
      return (ret, (qta''<:q:quota{q <= qta}), ctxt, origination)
      end

    | If bt _, Item (DBool true) rest ->
      step origination qta orig source amount ctxt bt rest

    | If _ bf, Item (DBool false) rest ->
      step origination qta orig source amount ctxt bf rest

    | Loop body, Item (DBool true) rest ->
      res <-- step origination qta orig source amount ctxt body rest;
      let (trans, qta', ctxt, origination) = res in
      if qta' <= 0 then
	fail Quota_exceeded
      else
	begin
	res <-- step origination (qta' - 1) orig source amount ctxt ui trans;
	let (ret, qta'', ctxt, origination) = res in
	return (ret, (qta''<:q:quota{q <= qta}), ctxt, origination)
	end

    | Loop _, Item (DBool false) rest ->
      logged_return (rest, qta, ctxt)

    | Dip b, Item v rest ->
      res <-- step origination qta orig source amount ctxt b rest;
      let (ret, qta, ctxt, origination) = res in
      return (Item v ret, qta, ctxt, origination)

    | Exec, Item arg (Item (DLambda (Lam _ _ lam _)) rest) ->
      // REMARK: Contrary to the OCaml code, we decrement [qta] from the start
      res <-- interp origination (qta - 1) orig source amount ctxt lam arg;
      let (ret, qta', ctxt, origination) = res in
      return (Item ret rest, (qta'<:q:quota{q <= qta}), ctxt, origination)

    | Lambda lam, rest ->
      logged_return (Item (DLambda lam) rest, qta - 1, ctxt)

    | Fail, _ ->
      fail Reject

    | Nop, stack ->
      logged_return (stack, qta, ctxt)

    (* comparison *)
    | Compare Bool_key, Item (DBool a) (Item (DBool b) rest) ->
      let cmpres = compare_bool a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare String_key, Item (DString a) (Item (DString b) rest) ->
      let cmpres = compare_string a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare Tez_key, Item (DTez a) (Item (DTez b) rest) ->
      let cmpres = compare_tez a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare Int_key, Item (DInt a) (Item (DInt b) rest) ->
      let cmpres = compare_int a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare Nat_key, Item (Nat a) (Item (Nat b) rest) ->
      let cmpres = compare_int a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare Key_hash_key, Item (DKey_hash a) (Item (DKey_hash b) rest) ->
      let cmpres = compare_keyhash a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Compare Timestamp_key, Item (Timestamp a) (Item (Timestamp b) rest) ->
      let cmpres = compare_timestamp a b in
      let cmpres = DInt cmpres in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    (* comparators *)
    | Eq, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres = 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Neq, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres <> 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Lt, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres < 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Le, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres <= 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Gt, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres > 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)

    | Ge, Item (DInt cmpres) rest ->
      let cmpres = compare_int cmpres 0 in
      let cmpres = DBool (cmpres >= 0) in
      logged_return (Item cmpres rest, qta - 1, ctxt)
(*
    (* protocol *)
    | Manager, Item (DContract _ _ contract) rest ->
      Contract.get_manager ctxt contract >>=? fun manager ->
      logged_return (Item manager rest, qta - 1, ctxt)
*)
    | Transfer_tokens storage_type,
      Item p (Item (DTez amount) (Item (DContract (TC tp Unit_t destination)) (Item sto Empty))) ->
      ctxt1 <-- spend_from_script ctxt source amount;
      ctxt2 <-- credit ctxt1 destination amount;
      let destination_script = get_script ctxt2 destination in
      let sto = unparse_data storage_type sto in
      ctxt3 <-- update_script_storage_and_fees ctxt source dummy_storage_fee sto;
      begin
      match begin // update succeeded, now execute the call
    	    match destination_script with
    	    | Error _ -> // a non scripted contract is a (unit,unit) contract
    		    if tp = Unit_t then Some(ctxt3,qta) else None
    		    // in the code it is a triple (ctxt, fuel, origination)
    		    // but I'm not sure what origination is and we
    		    // probably don't need it for now
    	    | Ok _ -> None
    		    // we will deal with this more complicated case when the
    		    // callee is a nontrivial contract later
    		  end
      with
      // the call failed, the error can be improved
      | None -> fail (GenericError "Wrong type of contract at Transfer_tokens")
      | Some(ctxt4, fuel) -> // the call succeeded
      script <-- get_script ctxt4 source;
      let (Script.Script _ storage) = script in begin
      match parse_data ctxt4 storage_type (Script.get_storage storage) with
      // storage corrupted, should not happen
      | None -> fail (GenericError "Corrupted Storage")
      | Some sto -> logged_return ((Item DUnit (Item sto Empty)), qta - 1, ctxt4)
      end end
      // begin
      // Contract.spend_from_script ctxt source amount >>=? fun ctxt ->
      // Contract.credit ctxt destination amount >>=? fun ctxt ->
      // Contract.get_script ctxt destination >>=? fun destination_script ->
      // let sto = unparse_data storage_type sto in
      // Contract.update_script_storage_and_fees ctxt source dummy_storage_fee sto >>=? fun ctxt ->
      // begin match destination_script with
      // 	| None ->
      // 	    (* we see non scripted contracts as (unit, unit) contract *)
      // 	    Lwt.return (ty_eq tp Unit_t |>
      // 			record_trace (Invalid_contract (loc, destination))) >>=? fun (Eq _) ->
      // 	    return (ctxt, qta, origination)
      // 	| Some { code ; storage } ->
      // 	    let p = unparse_data tp p in
      // 	    execute origination source destination ctxt storage code amount p qta
      // 	    >>=? fun (csto, ret, qta, ctxt, origination) ->
      // 	    Contract.update_script_storage_and_fees ctxt destination dummy_storage_fee csto >>=? fun ctxt ->
      // 	    trace
      // 	      (Invalid_contract (loc, destination))
      // 	      (parse_data ctxt Unit_t ret) >>=? fun () ->
      // 	    return (ctxt, qta, origination)
      // end >>=? fun (ctxt, qta, origination) ->
      // Contract.get_script ctxt source >>=? (function
      // 	  | None -> assert false
      // 	  | Some { storage = { storage } } ->
      // 	      parse_data ctxt storage_type storage >>=? fun sto ->
      // 	      logged_return ~origination (Item ((), Item (sto, Empty)), qta - 1, ctxt))
      // end
(*
    | Transfer_tokens storage_type,
      Item (p, Item (amount, Item ((tp, tr, destination), Item (sto, Empty)))) ->
      begin
      Contract.spend_from_script ctxt source amount >>=? fun ctxt ->
      Contract.credit ctxt destination amount >>=? fun ctxt ->
      Contract.get_script ctxt destination >>=? function
      | None -> fail (Invalid_contract (loc, destination))
      | Some { code ; storage } ->
	  let sto = unparse_data storage_type sto in
	  Contract.update_script_storage_and_fees ctxt source dummy_storage_fee sto >>=? fun ctxt ->
	  let p = unparse_data tp p in
	  execute origination source destination ctxt storage code amount p qta
	  >>=? fun (sto, ret, qta, ctxt, origination) ->
	  Contract.update_script_storage_and_fees ctxt destination dummy_storage_fee sto >>=? fun ctxt ->
	  trace
	    (Invalid_contract (loc, destination))
	    (parse_data ctxt tr ret) >>=? fun v ->
	  Contract.get_script ctxt source >>=? (function
	      | None -> assert false
	      | Some { storage = { storage } } ->
		  parse_data ctxt storage_type storage >>=? fun sto ->
		  logged_return ~origination (Item (v, Item (sto, Empty)), qta - 1, ctxt))
      end

    | Create_account,
      Item (manager, Item (delegate, Item (delegatable, Item (credit, rest)))) ->
	Contract.spend_from_script ctxt source credit >>=? fun ctxt ->
	Lwt.return Tez.(credit -? Constants.origination_burn) >>=? fun balance ->
	Contract.originate ctxt
	  origination
	  ~manager ~delegate ~balance
	  ?script:None ~spendable:true ~delegatable >>=? fun (ctxt, contract, origination) ->
	logged_return ~origination (Item ((Unit_t, Unit_t, contract), rest), qta - 1, ctxt)
*)
    | Default_account, Item (DKey_hash kh) rest ->
	let contract = Default kh in
	logged_return ((Item (DContract (TC Unit_t Unit_t (Default kh))) rest), qta - 1, ctxt)
(*
    | Create_contract (g, p, r),
      Item manager (Item delegate (Item spendable (Item delegatable
	(Item credit (Item (Lam (_, code)) (Item init rest)))))) ->
	let code, storage =
	  { code; arg_type = unparse_ty p;
	    ret_type       = unparse_ty r;
	    storage_type   =  unparse_ty g },
	  { storage        = unparse_data g init;
	    storage_type   = unparse_ty g } in
	Contract.spend_from_script ctxt source credit >>=? fun ctxt ->
	Lwt.return Tez.(credit -? Constants.origination_burn) >>=? fun balance ->
	Contract.originate ctxt
	  origination
	  ~manager ~delegate ~balance
	  ~script:({ code ; storage }, (dummy_code_fee, dummy_storage_fee))
	  ~spendable ~delegatable
	>>=? fun (ctxt, contract, origination) ->
	logged_return ~origination (Item (p, r, contract) rest, qta - 1, ctxt)
*)
    | Balance, rest ->
      begin
      balance <-- Storage.get_contract_balance ctxt source;
      logged_return (Item (DTez balance) rest, qta - 1, ctxt)
      end
(*
    | Now, rest ->
      let now = Timestamp.current ctxt in
      logged_return (Item now rest, qta - 1, ctxt)
*)
    | Check_signature, Item (DKey key) (Item (DPair (DSignature signature) (DString message)) rest) ->
      let res = CI.check_signature key signature message in
      // let message = MBytes.of_string message in
      // let res = Ed25519.Signature.check key signature message in
      logged_return (Item (DBool res) rest, qta - 1, ctxt)

    | Hash_key, Item (DKey key) rest ->
      logged_return (Item (DKey_hash (CI.public_key_hash key)) rest, qta -1, ctxt)

    | H ty, Item v rest ->
      let oexpr = (unparse_data ty v) in
      let hash = FStar_interface.hash_expr oexpr in
      logged_return (Item (DString hash) rest, qta - 1, ctxt)

    | Steps_to_quota, rest ->
      // REMARK: Contrary to OCaml code, we don't need to compute [abs (of_int qta)]
      logged_return (Item (Nat qta) rest, qta - 1, ctxt)

    | Source ta tb, rest ->
      logged_return (Item (DContract (Definitions.TC ta tb orig)) rest, qta - 1, ctxt)

    | Amount, rest ->
      logged_return (Item (DInt amount) rest, qta - 1, ctxt)

    | i,st -> fail (Runtime_contract_error 
           ((instr_to_string i) ^ "\non stack\n" ^(string_of_stack st)))
    end

and interp origination qta orig source amount ctxt code arg =
  res <-- step origination qta orig source amount ctxt code (Item arg Empty);
  match res with
  | Item ret Empty, qta', ctxt, origination ->
    return (ret, qta', ctxt, origination)
  | _ ->
    fail Reject // Impossible for well-typed programs

// and execute origination orig source ctxt storage script amount arg qta =
//   let { Script.storage ; storage_type } = storage in
//   let { Script.code ; arg_type ; ret_type } = script in
//   (Lwt.return (parse_ty arg_type)) >>=? fun (Ex_ty arg_type) ->
//   (Lwt.return (parse_ty ret_type)) >>=? fun (Ex_ty ret_type) ->
//   (Lwt.return (parse_ty storage_type)) >>=? fun (Ex_ty storage_type) ->
//   let arg_type_full = Pair_t (arg_type, storage_type) in
//   let ret_type_full = Pair_t (ret_type, storage_type) in
//   trace
//     (Ill_typed_contract (code, arg_type, ret_type, storage_type, []))
//     (parse_lambda ~storage_type ctxt arg_type_full ret_type_full code) >>=? fun lambda ->
//   parse_data ctxt arg_type arg >>=? fun arg ->
//   parse_data ctxt storage_type storage >>=? fun storage ->
//   trace
//     (Runtime_contract_error (source, code, arg_type, ret_type, storage_type))
//     (interp ?log origination qta orig source amount ctxt lambda (arg, storage))
//   >>=? fun (ret, qta, ctxt, origination) ->
//   let ret, storage = ret in
//   return (unparse_data storage_type storage,
//           unparse_data ret_type ret,
//           qta, ctxt, origination)
