(**
 * This module defines a typechecker for an untyped representation
 * of Michelson expressions.
 *
 * Tis module should enable to translate a successfully typechecked
 * expression to its typed representation, but we're not there yet.
 *
 * This module also defines [ueval], a function to evaluate
 * untyped expressions directly failing on type errors, and some simple contract
 * examples. They should be moved somewhere else.
 *)
module Tezos.AbstractInterpreter

open Tezos.Primitives
open Tezos.Definitions
open Tezos.UntypedDefinitions
open Tezos.Serialization
open Tezos.TezRepr
open Tezos.Storage
open Tezos.Error
module S = Tezos.ScriptRepr

(**
 * These are the possible successful results of the type checker for
 * untyped expressions.
 *
 * REMARK: [Failed i] is not a failure, but the successful type of an
 * expression that fails.
 * E.g. [parse_uinstr ctxt Fail bef == fun (aft:stack_ty). instr bef aft]
 *)
type judgement =
 | Typed      : stack_ty -> judgement
 | Failed     : judgement
 | Untypeable : judgement

(**
 * This is used for merging the typing results of branches,
 * When the result of typecheking one branch is [Typed aft] and for the other is
 * [Failed], the overall type is [Typed aft], because programs that fail
 * can be given any stack result type.
 *)
val merge_judgements: judgement -> judgement -> judgement
let merge_judgements j1 j2 =
  match j1, j2 with
  | Typed st1, Typed st2 -> if st1 = st2 then Typed st1 else Untypeable
  | Typed st,  Failed    -> Typed st
  | Failed,    Typed st  -> Typed st
  | Failed,    Failed    -> Failed
  | _                    -> Untypeable

val interp_ty_abs: ty -> Type0
let rec interp_ty_abs =
  function
  | Unit_t -> unit
  | Int_t -> int
  | Nat_t -> nat
  | Signature_t -> signature
  | String_t -> string
  | Tez_t -> tez
  | Key_t -> key
  | Key_hash_t -> pkeyhash
  | Timestamp_t -> timestamp
  | Bool_t -> bool
  | Pair_t ta tb ->
    let a = interp_ty_abs ta in
    let b = interp_ty_abs tb in
    a * b
  | Union_t ta tb ->
    let a = interp_ty_abs ta in
    let b = interp_ty_abs tb in
    either a b
  | Map_t tk tv ->
    let k = interp_comp_ty tk in
    let v = interp_ty_abs tv in
    myMap k v
  | Set_t tk ->
    let k = interp_comp_ty tk in
    mySet k
  | Option_t tv ->
    let v = interp_ty_abs tv in
    option v
  | Lambda_t ta tb ->
    uinstr
  | Contract_t targ tret ->
    uinstr
  | List_t ta ->
    let a = interp_ty_abs ta in
    list a


val parse_uinstr: context -> uinstr -> stack_ty -> judgement
let rec parse_uinstr ctxt i bef =
  match i, bef with
  | Fail, _ -> Failed

  | Nop, _ -> Typed bef

  | Seq c1 c2, bef ->
    begin
    match parse_uinstr ctxt c1 bef with
    | Typed trans -> parse_uinstr ctxt c2 trans
    | Failed -> Untypeable // Failure in non-tail position
    | Untypeable -> Untypeable
    end

  | If ct cf, Item_t Bool_t rest ->
    let stt = parse_uinstr ctxt ct rest in
    let stf = parse_uinstr ctxt cf rest in
    merge_judgements stt stf

  | Drop, Item_t _ rest -> Typed rest

  | Dup, Item_t t rest -> Typed (Item_t t (Item_t t rest))

  | Swap, Item_t t1 (Item_t t2 rest) -> Typed (Item_t t2 (Item_t t1 rest))

  | Loop body, Item_t Bool_t rest ->
    begin
    match parse_uinstr ctxt body rest with
    | Typed (Item_t Bool_t rest') ->
      if rest = rest' then Typed rest else Untypeable
    | Failed ->
      // If the body fails, the loop is typeable
      Typed rest
    | _ -> Untypeable
    end

  | Lambda (Lam arg ret c e), rest ->
    begin
    match parse_uinstr ctxt c (Item_t arg Empty_t) with
    | Typed (Item_t ret' Empty_t) ->
      if ret = ret' then Typed (Item_t (Lambda_t arg ret) rest) else Untypeable
    | Failed -> Typed (Item_t (Lambda_t arg ret) rest)
    | _ -> Untypeable
    end

  | Eq, Item_t Int_t rest  -> Typed (Item_t Bool_t rest)

  | Ge, Item_t Int_t rest  -> Typed (Item_t Bool_t rest)

  | Neq, Item_t Int_t rest  -> Typed (Item_t Bool_t rest)

  | Mul_intint, Item_t Int_t (Item_t Int_t rest) -> Typed (Item_t Int_t rest)

  | Add_intint, Item_t Int_t (Item_t Int_t rest) -> Typed (Item_t Int_t rest)

  | Sub_int, Item_t Int_t (Item_t Int_t rest) -> Typed (Item_t Int_t rest)

  // | Const t v, resty -> if check_type ctxt v t then Typed (Item_t t resty) else Failed (Const t v)

  | Const_int v, rest -> Typed (Item_t Int_t rest)

  | Const_bool v, rest -> Typed (Item_t Bool_t rest)

  | Const_tez v, rest -> Typed (Item_t Tez_t rest)

  | Const_unit, rest -> Typed (Item_t Unit_t rest)

  | Dip c, Item_t t rest ->
    begin
    match parse_uinstr ctxt c rest with
    | Typed aft -> Typed (Item_t t aft)
    | Failed -> Untypeable // Failure in non-tail position
    | Untypeable -> Untypeable
    end

  | If_none bt bf, Item_t (Option_t ta) rest ->
    let stt = parse_uinstr ctxt bt rest in
    let stf = parse_uinstr ctxt bf (Item_t ta rest) in
    merge_judgements stt stf

  | Cdr, Item_t (Pair_t _ b) rest -> Typed (Item_t b rest)

  | Car, Item_t (Pair_t a _) rest -> Typed (Item_t a rest)

  | H t1 , Item_t t rest -> if t1 = t then Typed (Item_t String_t rest) else Untypeable

  | Check_signature, Item_t Key_t (Item_t (Pair_t Signature_t String_t) rest) ->
    Typed (Item_t Bool_t rest)

  | Cons_pair, Item_t ta (Item_t tb rest) -> Typed (Item_t (Pair_t ta tb) rest)

  | Map_get, Item_t ta (Item_t (Map_t ta' tb) rest) ->
    if ta = ty_of_comp_ty ta' then Typed (Item_t (Option_t tb) rest) else Untypeable

  | Compare t1, Item_t ta (Item_t tb rest) ->
    if (ty_of_comp_ty t1 = ta && ta = tb) then Typed (Item_t Int_t rest) else Untypeable

  | Map_reduce,
    Item_t (Lambda_t (Pair_t (Pair_t ta tv) tres) tres')
           (Item_t (Map_t ta' tv') (Item_t tres'' rest)) ->
    if ta = ty_of_comp_ty ta' && tv = tv' && tres = tres' && tres' = tres'' then
      Typed (Item_t tres rest)
    else Untypeable

  | Transfer_tokens storage_type,
    Item_t ta (Item_t Tez_t (Item_t (Contract_t ta' tb) (Item_t tg Empty_t))) ->
    if tg = storage_type then
    Typed (Item_t tb (Item_t tg Empty_t)) else Untypeable

  | Exec, Item_t ta (Item_t (Lambda_t ti to) resty) ->
    if ta = ti then Typed (Item_t to resty) else Untypeable

  | Default_account, Item_t Key_t resty -> Typed (Item_t (Contract_t Unit_t Unit_t) resty)

  | _ -> Untypeable


(**
 * These definitions used to be mutually recursive with [parse_uinstr]
 * They were introduced to typecheck [Const v], but now [uinstr] specializes
 * the type of constants
 *)
val check_type:	     context -> tagged_data -> ty -> bool
val check_map_type:  context -> myMap tagged_data tagged_data -> comparable_ty
  -> ty -> bool
val check_set_type:  context -> mySet tagged_data -> comparable_ty -> bool
val check_list_type: context -> list tagged_data -> ty -> bool

let rec check_type ctxt d t =
  match d, t with
  | DInt _, Int_t -> true

  | Nat _, Nat_t -> true

  | DString _, String_t -> true

  | DMap m, Map_t tk tv -> check_map_type ctxt m tk tv

  | DUnit, Unit_t -> true

  | DBool b, Bool_t -> true

  | DString s, String_t -> true

  | DKey k, Key_t -> true

  | Timestamp t, Timestamp_t -> true

  | DTez t, Tez_t -> true

  | DPair a b, Pair_t ta tb -> check_type ctxt a ta && check_type ctxt b tb

  | DMap m, Map_t ta tb -> check_map_type ctxt m ta tb

  | DLambda (Lam ta tb ui1 expr), Lambda_t ta' tb' -> ta = ta' && tb = tb' &&
    begin match parse_lambda ctxt ta tb expr with
    | Some(ta',tb',e1,ui2) ->
      ta = ta' && tb = tb' //&& ui1 = ui2 // TS: probably we want to keep this for later
      //&& (parse_uinstr ui (Item_t ta Empty_t) = Typed (Item_t tb Empty_t) )
    | None -> false
    end

  | DOption None, Option_t t -> true

  | DOption (Some v), Option_t t -> check_type ctxt v t

  | DContract (TC ta tb h), Contract_t ta' tb' ->
    ta = ta' && tb = tb' && true // TODO to be replaced by check of handle

  | DList l, List_t t -> check_list_type ctxt l t

  | _ , _ -> false

and check_map_type ctxt m ctk tv =
  // The following does not work because of the termination checker
  // let tk = (ty_of_comp_ty ctk) in
  // map_fold_left tagged_data tagged_data  m (fun b k v -> b && check_type k tk && check_type v tv) true
  // so instead we use a trick because we know maps are (for now) lists
  match m with
   | [] -> true
   | (k,v)::xs -> check_type ctxt k (ty_of_comp_ty ctk) && check_type ctxt v tv && check_map_type ctxt xs ctk tv

and check_set_type ctxt s ts =
  // Same problem as maps, same workaround
  // set_fold tagged_data s (fun b v -> b && check_type v (ty_of_comp_ty ts)) true
  match s with
   | [] -> true
   | x::xs -> check_type ctxt x (ty_of_comp_ty ts) && check_set_type ctxt xs ts

and check_list_type ctxt l t =
  match l with
  | [] -> true
  | x::xs -> check_type ctxt x t && check_list_type ctxt xs t


(** Evaluation of untyped scripts *)

type stack =
| UItem:x:tagged_data -> rest:stack -> stack
| UEmpty:stack

val check_stack_type: context -> stack -> sty:stack_ty -> Tot bool (decreases sty)
let rec check_stack_type ctxt st sty =
  match st, sty with
  | UEmpty , Empty_t -> true
  | UItem v r, Item_t tv tr ->
    check_type ctxt v tv &&
    check_stack_type ctxt r tr
  | _ -> false

noeq type result =
| Failure: uinstr -> result
| Partial: fuel:nat -> ctxt:context -> st:stack -> result
| OutofFuel: uinstr -> stack -> context -> result

val correct_output: context -> stack -> result -> stack_ty -> judgement -> bool
let correct_output ctxt st r sty_in j =
  // SZ: Unsure what's the intent of this, but the `st` variable used to be shadowed below
  match r, j with
  | Partial f _ st', Typed sty_out ->
     not (check_stack_type ctxt st sty_in) ||
     check_stack_type ctxt st' sty_out
  | _ -> true


assume val hash: tagged_data -> string
assume val check_signature: tagged_data -> tagged_data -> tagged_data -> bool
assume val get: myMap tagged_data tagged_data -> tagged_data -> option tagged_data

#set-options "--z3rlimit 50 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 1"

(**
 * Untyped evaluation
 * The arguments are
 * - fuel: the analog of qta in Ocaml, destined to become gas?
 * - uinstr: the program itself
 * - stack: the input stack
 * - ctxt: the current context (can be thought of as the blockchain)
 * - source: the current contract as it is stored in the blockchain
 * The result is either
 * - Partial f' ctxt' st', which means the computation succeeded
 *   with output stack st', context ctxt' and fuel f'
 * - Outoffuel ui' st' ctxt': we ran out of fuel on opcode ui',
 *   with stack st' and context ctxt'
 * - Failure ui': the execution failed. There may still be confusion
 *   as to whether two different notions of failure are being conflated here:
 *   running the opcode Fail, or encountering an unexpected situation
 *   (having an ill-typed stack for example, which should not happen if the
 *   program has been checked to be well-typed.
 * May want to prove this refinement of the result:
 * [{forall (sty_in:stack_ty). correct_output st r sty_in (parse_uinstr ui sty_in)}]
 *)
val ueval: fuel:nat -> ui:uinstr -> stack -> context -> contract ->
  Tot (r:result{Partial? r ==> Partial?.fuel r <= fuel}) (decreases %[fuel; ui])
let rec ueval fuel ui st ctxt source =
  match fuel with
  | 0 -> OutofFuel ui st ctxt
  | _ ->
    match ui, st with
    | Drop, UItem v r -> Partial (fuel - 1) ctxt r

    | Dup, UItem v r -> Partial (fuel - 1) ctxt (UItem v (UItem v r))

    | Swap, UItem v (UItem v' r) -> Partial (fuel - 1) ctxt (UItem v' (UItem v r))

    | Car, UItem (DPair u _) r -> Partial (fuel - 1) ctxt (UItem u r)

    | Cdr, UItem (DPair _ v) r -> Partial (fuel - 1) ctxt (UItem v r)

    | Cons_pair, UItem v (UItem v' r) ->
      Partial (fuel - 1) ctxt (UItem (DPair v v') r)

    | Or, UItem (DBool v) (UItem (DBool v') r) -> 
      Partial (fuel - 1) ctxt (UItem (DBool (v || v')) r)

    | Or, UItem (DBool v) (UItem (DBool v') r) -> 
      Partial (fuel - 1) ctxt (UItem (DBool (v && v')) r)

    | Mul_intint, UItem (DInt v) (UItem (DInt v') r) ->
      Partial (fuel - 1) ctxt (UItem (DInt FStar.Mul.(v * v')) r)

    | Add_intint, UItem (DInt v) (UItem (DInt v') r) ->
      Partial (fuel - 1) ctxt (UItem (DInt (v + v')) r)

    | Sub_int, UItem (DInt v) (UItem (DInt v') r) ->
      Partial (fuel - 1) ctxt (UItem (DInt (v - v')) r) // TH: FIXME (types are more general)

    | Const_int n, _ -> Partial (fuel - 1) ctxt (UItem (DInt n) st)

    | Const_tez n, _ -> Partial (fuel - 1) ctxt (UItem (DTez n) st)

    | Compare Int_key, UItem (DInt v) (UItem (DInt v') r) ->
      Partial (fuel - 1) ctxt (UItem (DInt (compare_int v v')) r)

    | Fail, _ -> Failure Fail

    // SZ: We don't decrease fuel in Nop, an artificial opcode
    | Nop, st -> Partial fuel ctxt st

    | Seq c1 c2, st ->
      begin
      match ueval fuel c1 st ctxt source with
      | Failure ui -> Failure ui
      | OutofFuel ui s ctxt' -> OutofFuel ui s ctxt'
      | Partial fuel' ctxt' st' -> ueval fuel' c2 st' ctxt' source
      end

    | If bt bf, UItem (DBool true) rest ->
      ueval fuel bt rest ctxt source

    | If bt bf, UItem (DBool false) rest ->
      ueval fuel bf rest ctxt source

    | If_none bt bf, UItem (DOption ov) r ->
      begin
      match ov with
      | Some v -> ueval fuel bf (UItem v r) ctxt source
      | None   -> ueval fuel bt r ctxt source
      end

    | Dip c, UItem v r ->
      begin
      match ueval fuel c r ctxt source with
      | Failure ui     -> Failure ui
      | OutofFuel ui s ctxt' -> OutofFuel ui s ctxt'
      | Partial fuel' ctxt' st'  -> Partial fuel' ctxt' (UItem v st')
      end

    | Loop body, UItem (DBool true) r ->
      begin
      match ueval fuel body r ctxt source with
      | Failure i         -> Failure i
      | OutofFuel ui st ctxt'   -> OutofFuel ui st ctxt'
      | Partial fuel' ctxt' st' ->
        if fuel' > 0 then ueval (fuel' - 1) ui st' ctxt' source else OutofFuel ui st ctxt'
      end

    | Loop body, UItem (DBool false) r -> Partial fuel ctxt r

    | Eq, UItem (DInt v) r -> Partial fuel ctxt (UItem (DBool (v = 0)) r)

    | Ge, UItem (DInt v) r -> Partial fuel ctxt (UItem (DBool (v >= 0)) r)

    | Neq, UItem (DInt v) r -> Partial fuel ctxt (UItem (DBool (v <> 0)) r)

    | H t1, UItem v r -> if check_type ctxt v t1 then Partial fuel ctxt (UItem (DString (hash v)) r) else Failure ui

    | Check_signature, UItem k (UItem (DPair sign str) r) ->
      Partial fuel ctxt (UItem (DBool (check_signature k sign str)) r)

    | Map_get, UItem k (UItem (DMap m) r) ->
      Partial fuel ctxt (UItem (DOption (get m k)) r)

    | Lambda lam, st -> Partial (fuel - 1) ctxt (UItem (DLambda lam) st)

    | Exec, UItem arg (UItem (DLambda (Lam ta tb ui' e)) rest) ->
	    begin match ueval (fuel-1) ui' (UItem arg UEmpty) ctxt source with
		  | Partial f1 ctxt' (UItem res UEmpty) -> Partial f1 ctxt' (UItem res rest)
		  | Partial _ _ _ -> Failure ui // should never happen if the program is well-typed
		  | other -> other
		  end

    | Default_account, UItem (DKey_hash kh) rest -> Partial fuel ctxt (UItem (DContract (TC Unit_t Unit_t (Default kh))) rest)

    | Transfer_tokens storage_type, UItem p (UItem (DTez amount) (UItem (DContract (TC tp Unit_t destination)) (UItem sto UEmpty))) ->
      begin // first attempt to move the funds from the source account
      match spend_from_script ctxt source amount with
      | Error _ -> Failure ui
      | Ok ctxt1 ->
	begin // then attempt to credit the funds to the destination account
	match credit ctxt1 destination amount with
	| Error _ -> Failure ui
	| Ok ctxt2 ->
	  // since we are calling a contract, we need to get its code
	  let destination_script = get_script ctxt2 destination in
	  // before making the call, we need to update the source contract's
	  // storage with the one put on the stack: first serialize it...
	  let sto = unparse_data storage_type sto in
	  begin // ... and then do the actual update
	  match update_script_storage_and_fees ctxt source dummy_storage_fee sto with
	  | Error _ -> Failure ui
	  | Ok ctxt3 ->
	    match begin // update succeeded, now execute the call
		   match destination_script with
		   | Error _ -> // a non scripted contract is a (unit,unit) contract
		     if tp = Unit_t then Some(ctxt3,fuel) else None
			// in the code it is a triple (ctxt, fuel, origination)
			// but I'm not sure what origination is and we
			// probably don't need it for now
		   | Ok _ -> None
		      // we will deal with this more complicated case when the
		      // callee is a nontrivial contract later
		  end
	    with
	    | None -> Failure ui // the call failed
	    | Some(ctxt4, fuel) -> // the call succeeded
	      begin match get_script ctxt4 source with
		    | Error _ -> Failure ui//should never happen
		    | Ok (S.Script _ storage) ->
		    begin
		    // we get back the source script's storage to put it back
		    // on the stack
		      match parse_data ctxt4 storage_type (S.get_storage storage) with
		      | None -> Failure ui // storage corrupted, should not happen
		      | Some sto ->
			Partial (fuel-1) ctxt4 (UItem DUnit (UItem sto UEmpty))
		    end
	      end
	  end
      end
      end
    | _, _ -> Failure ui



let (>>) = Seq

let cadr = Car >> Cdr

let cdar = Cdr >> Car

let rec dup_rec (n : nat) =
  match n with
  | 0 -> Nop
  | 1 -> Dup
  | n -> Dip (dup_rec (n-1)) >> Swap


let duuuuuup = dup_rec 6

let test ctxt0 =
  parse_uinstr ctxt0 duuuuuup
    (Item_t Int_t (Item_t Int_t (Item_t Int_t (Item_t Int_t
      (Item_t String_t (Item_t Bool_t Empty_t))))))

let rec dip_rec (n:nat) c =
  match n with
  | 0 -> Nop
  | 1 -> Dip c
  | n -> (dip_rec (n-1) (Dip c))

let diip = dip_rec 2
let diiip = dip_rec 3
let diiiip = dip_rec 4

let ifcmpge t bt bf = (Compare t) >> Ge >> If bt bf

let lambda_input_type =
 Pair_t (Pair_t String_t Signature_t) (Pair_t (Pair_t (Map_t String_key Key_t) String_t) Int_t)

let lambda_output_type = Pair_t (Pair_t (Map_t String_key Key_t) String_t) Int_t

let multisig_storage_type = Pair_t (Map_t String_key Key_t) Int_t

let multisig_param_type =
 Pair_t (Pair_t (Contract_t Unit_t Unit_t) Tez_t) (Map_t String_key Signature_t)

let multisig_input_type =
  Item_t (Pair_t (Pair_t Tez_t multisig_param_type) multisig_storage_type) Empty_t

let multisig_output_type =
  Item_t (Pair_t Unit_t multisig_storage_type) Empty_t

let const_int v = Const_int v

let lambda_multisig =
  ((Dup >> Cdr >> Swap >> Car  >>
   Dup >> Cdr >> Swap >> Car >>
   diip (( Dup >> Cdr >> Swap>> Car )) >>
   diip (( Dup >> Cdr >> Swap>> Car )) >> Swap >>
   Dip
     (( Dip (( Dup )) >> Map_get >>
       If_none (( Fail )) (( Nop ))
     )) >>
   diip	 (( Swap >> Dup )) >>
   diiip (( Swap >> Cons_pair >> Swap )) >>
   Swap >> Dip (( Cons_pair ))  >>
   Check_signature >>
   If (( Const_int 1 >> Add_intint )) (( Fail )) >>
   Swap >> Cons_pair
  ))

let lambda_multisig_v ctxt0  =
  parse_uinstr ctxt0 lambda_multisig (Item_t lambda_input_type Empty_t)

let multisig =
  Dup >> Dup >> Cdr >> Swap >> cadr >> Dip (( Dup )) >>
  Dip (( Cdr >> Swap >> Car )) >>
  Dup >> Cdr >> Swap >> Car >>
  Dup >> H (Pair_t (Lambda_t Unit_t Unit_t) Tez_t) >>
  duuuuuup>> cdar >> Cons_pair >>
  Const_int 0 >> Swap >> Cons_pair >>
  Dip (( Swap )) >> Swap >>
  Lambda (Lam lambda_input_type lambda_output_type lambda_multisig  (S.String "todo")) >>
  Map_reduce >>
  Cdr >> Dip (( Swap >> Drop >> Swap )) >>
  ifcmpge Int_key
    ((
      Dup >> Cdr >> Swap >> Car >> Const_unit >> Dip (( Swap )) >> diiip (( Cdr )) >>
      Transfer_tokens multisig_storage_type >>
      Drop >> Const_unit >> Cons_pair
    ))
    ((
      Fail
    ))

let v_multisig  ctxt0 =
  parse_uinstr ctxt0 multisig multisig_input_type

// assume val ctxt0 : context

// let check_multisig  =
//   assert_norm (parse_uinstr ctxt0 multisig multisig_input_type = Typed multisig_output_type)
