module Tezos.Translation

module A = Tezos.AbstractInterpreter
module U = Tezos.UntypedDefinitions
module L = Tezos.LanguageGadt

open L
open Tezos.Error
open Tezos.ScriptRepr
open Tezos.Storage
open Tezos.Definitions
module F = FStar_interface
module CI = CryptoInterface

val strip: #a:stack_ty -> #b:stack_ty -> i:instr a b -> Tot U.uinstr (decreases i)
let rec strip #a #b =
  function
  | L.Seq c1 c2 -> U.Seq (strip c1) (strip c2)
  | If bt bf -> U.If (strip bt) (strip bf)
  | If_none bt bf -> U.If_none (strip bt) (strip bf)
  | Dip c -> U.Dip (strip c)
  | Loop b -> U.Loop (strip b)
  | Drop -> U.Drop
  | Dup -> U.Dup
  | Swap -> U.Swap
  //| Const_unit () -> U.Const Unit_t U.DUnit
  | Const_int v -> U.Const_int v
  | Unit -> U.Const_unit
  | Car -> U.Car
  | Cdr -> U.Cdr
  | Pair -> U.Cons_pair
  | Or -> U.Or
  | And -> U.And
  | Mul_intint -> U.Mul_intint
  | Add_intint -> U.Add_intint
  | Sub_int -> U.Sub_int
  | Eq -> U.Eq
  | Ge -> U.Ge
  | Neq -> U.Neq
  | Hash -> let Item_t t _ = a in U.H t
  | Check_signature -> U.Check_signature
  | Get -> U.Map_get // TODO: check this is valid
  // | Lambda (Lam t1 t2 l e) -> // TSP: TODO: this case needs to be redone after recent changes
  //   let Item_t (Lambda_t targ tret) resty = b in
  //   U.Lambda (Lam targ tret (strip #(Item_t targ Empty_t) #(Item_t tret Empty_t) ( l)) e)
  | Compare #t -> U.Compare t
  | Fail -> U.Fail
  | Nop -> U.Nop
  | Map_reduce -> U.Map_reduce
  | _ -> U.Nop

(* opening here to prevent name capture above *)
open U
open FStar.All

val expr_to_ty : expr -> tzresult ty
val expr_to_data : context -> ty -> expr -> tzresult tagged_data
val expr_to_data_list : context -> ty -> list expr -> tzresult (list tagged_data)

let rec expr_to_ty =
  function
  | Prim "unit" [] -> return Unit_t
  | Prim "int" [] -> return (Int_t)
  | Prim "nat" [] -> return (Nat_t)
  | Prim "string" [] -> return String_t
  | Prim "tez" [] -> return Tez_t
  | Prim "bool" [] -> return Bool_t
  | Prim "key" [] -> return Key_t
  | Prim "key_hash" [] -> return Key_hash_t
  | Prim "timestamp" [] -> return Timestamp_t
  | Prim "signature" [] -> return Signature_t
  // | Prim "contract" [ utl; utr ] ->
  //     parse_ty utl >>? fun (Ex_ty tl) ->
  //     parse_ty utr >>? fun (Ex_ty tr) ->
  //     return (Contract_t (tl, tr))

  | Prim "pair" [ utl; utr ] ->
    tl <-- expr_to_ty utl;
    tr <-- expr_to_ty utr;
    return (Pair_t tl tr)

  // | Prim "or", [ utl; utr ], _) ->
  //     parse_ty utl >>? fun (Ex_ty tl) ->
  //     parse_ty utr >>? fun (Ex_ty tr) ->
  //     return (Union_t (tl, tr))
  // | Prim "lambda", [ uta; utr ], _) ->
  //     parse_ty uta >>? fun (Ex_ty ta) ->
  //     parse_ty utr >>? fun (Ex_ty tr) ->
  //     return (Lambda_t (ta, tr))
  | Prim "option" [ ut ] ->
    t <-- expr_to_ty ut;
    return (Option_t t)

  | Prim "list" [ ut ] ->
    t <-- expr_to_ty ut;
    return (List_t t)

  // | Prim "set", [ ut ], _) ->
  //     parse_comparable_ty ut >>? fun (Ex_comparable_ty t) ->
  //     return (Set_t t)
  // | Prim "map", [ uta; utr ], _) ->
  //     parse_comparable_ty uta >>? fun (Ex_comparable_ty ta) ->
  //     parse_ty utr >>? fun (Ex_ty tr) ->
  //     return (Map_t (ta, tr))
  // | Prim (loc, ("pair" | "or" | "set" | "map"
  //              | "list" | "option"  | "lambda"
  //              | "unit" | "signature"  | "contract"
  //              | "int" | "nat"
  //              | "string" | "tez" | "bool"
  //              | "key" | "key_hash" | "timestamp" as prim), l, _) ->
  //     error (Invalid_arity (loc, prim, 0, List.length l)
  | expr ->
    fail (Unimplemented ("expr_to_ty: "^(Tezos.ScriptRepr.expr_to_string expr)))



// Until the int_of_string issue is resolved
let int_of_string v = FStar_interface.int_of_string v

let rec expr_to_data_list ctxt t le = match le with
  | [] -> return []
  | hd::tl ->
    restl <-- expr_to_data_list ctxt t tl;
    reshd <-- expr_to_data ctxt t hd;
    return (reshd::restl)

and expr_to_data ctxt t e = match t, e with
  | Unit_t, Prim "Unit" [] -> return DUnit
  (* Booleans *)
  | Bool_t, Prim "True" [] -> return (DBool true)
  | Bool_t, Prim "False" [] -> return (DBool false)
  // | Bool_t, Prim (loc, ("True" | "False" as c), l, _) ->
  //	 traced (fail (Invalid_arity (loc, c, 0, List.length l)))
  // | Bool_t, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "True" ; "False" ]))
  (* Strings *)
  | String_t, String v -> return (DString v)
  // | String_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  (* Integers *)
  | Int_t, Int v ->
      begin match int_of_string v with
	| None -> fail (GenericError "The value should be an integer")
	| Some v -> return (DInt v)
      end
  | Nat_t, Int v ->
begin match int_of_string v with
  | None -> fail (GenericError "The value should be an integer")
  | Some v -> if v >= 0 then
	     return (Nat v) else
	     fail (GenericError "Can't interpret a negative number as a Nat_t")
end
  | Tez_t, String v -> begin
	match F.tez_of_string_as_int64 v with
	| None -> fail (GenericError "Couldn't parse amount in tez")
	| Some tez -> if tez >= 0 then return (DTez tez) else fail (GenericError "Negative amount")
    end
  // | Tez_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  // (* Timestamps *)
  // | Timestamp_t, (Int (_, v)) -> begin
  //	 match (Timestamp.of_seconds v) with
  //	 | Some v -> return v
  //	 | None -> fail (error ())
  //   end
  // | Timestamp_t, String (_, s) -> begin try
  //	   match Timestamp.of_notation s with
  //	   | Some v -> return v
  //	   | None -> fail (error ())
  //	 with _ -> fail (error ())
  //   end
  // | Timestamp_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ; Int_kind ], kind expr)))
  // (* IDs *)
  | Key_t, String s ->
      begin

	  return (DKey (CI.pkey_of_b58check_exn s))
      end
  // | Key_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  | Key_hash_t, String s ->
	  return (DKey_hash (CI.pkeyhash_of_b58check_exn s))
  // | Key_hash_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  // (* Signatures *)
  | Signature_t, String s -> begin
	match CI.parse_signature s with
	| Some s -> return (DSignature s)
	| None -> fail (GenericError "Invalid signature")
    end
  // | Signature_t, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  // (* Contracts *)
  // | Contract_t (ty1, ty2), String (loc, s) ->
  //	 traced @@
  //	 (Lwt.return (Contract.of_b58check s)) >>=? fun c ->
  //	 parse_contract ctxt ty1 ty2 loc c >>=? fun _ ->
  //	 return (ty1, ty2, c)
  // | Contract_t _, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
  // (* Pairs *)
  | Pair_t ta tb, Prim "Pair" [ va; vb ] ->
      va <-- expr_to_data ctxt ta va;
      vb <-- expr_to_data ctxt tb vb;
      return (DPair va vb)
  // | Pair_t _, Prim (loc, "Pair", l, _) ->
  //	 fail @@ Invalid_arity (loc, "Pair", 2, List.length l)
  // | Pair_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "Pair" ]))
  // (* Unions *)
  // | Union_t (tl, _), Prim (_, "Left", [ v ], _) ->
  //	 traced @@
  //	 parse_data ?type_logger ctxt tl v >>=? fun v ->
  //	 return (L v)
  // | Union_t _, Prim (loc, "Left", l, _) ->
  //	 fail @@ Invalid_arity (loc, "Left", 1, List.length l)
  // | Union_t (_, tr), Prim (_, "Right", [ v ], _) ->
  //	 traced @@
  //	 parse_data ?type_logger ctxt tr v >>=? fun v ->
  //	 return (R v)
  // | Union_t _, Prim (loc, "Right", l, _) ->
  //	 fail @@ Invalid_arity (loc, "Right", 1, List.length l)
  // | Union_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "Left" ; "Right" ]))
  // (* Lambdas *)
  // | Lambda_t (ta, tr), (Seq _ as script_instr) ->
  //	 traced @@
  //	 parse_lambda ?type_logger ctxt ta tr script_instr
  // | Lambda_t _, expr ->
  //	 traced (fail (Invalid_kind (location expr, [ Seq_kind ], kind expr)))

  (* Options *)
  | Option_t t, Prim "Some" [ v ] ->
    v <-- expr_to_data ctxt t v;
    return (DOption (Some v))

  | Option_t _, Prim "None" [] ->
    return (DOption None)

  // | Option_t _, Prim (loc, "Some", l, _) ->
  //	 fail @@ Invalid_arity (loc, "Some", 1, List.length l)
  // | Option_t _, Prim (loc, "None", l, _) ->
  //	 fail @@ Invalid_arity (loc, "None", 0, List.length l)
  // | Option_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "Some" ; "None" ]))

  (* Lists *)
  | List_t t, Prim "List" vs ->
    res <-- expr_to_data_list ctxt t vs;
    return (DList res)

  // | List_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "List" ]))
  // (* Sets *)
  // | Set_t t, (Prim (loc, "Set", vs, _) as expr) ->
  //	 fold_left_s
  //	   (fun (last_value, set) v ->
  //	      parse_comparable_data ?type_logger ctxt t v >>=? fun v ->
  //	      begin match last_value with
  //	       | Some value ->
  //		   if Compare.Int.(0 <= (compare_comparable t value v))
  //		   then
  //		     if Compare.Int.(0 = (compare_comparable t value v))
  //		     then fail (Duplicate_set_values (loc, expr))
  //		     else fail (Unordered_set_values (loc, expr))
  //		   else return ()
  //	       | None -> return ()
  //	      end >>=? fun () ->
  //	      return (Some v, set_update v true set))
  //	   (None, empty_set t) vs >>|? snd |> traced
  // | Set_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "Set" ]))
  // (* Maps *)
  // | Map_t (tk, tv), (Prim (loc, "Map", vs, _) as expr) ->
  //	 (fold_left_s
  //	   (fun (last_value, map) -> function
  //	      | Prim (_, "Item", [ k; v ], _) ->
  //		  parse_comparable_data ?type_logger ctxt tk k >>=? fun k ->
  //		  parse_data ?type_logger ctxt tv v >>=? fun v ->
  //		  begin match last_value with
  //		   | Some value ->
  //		       if Compare.Int.(0 <= (compare_comparable tk value k))
  //		       then
  //			 if Compare.Int.(0 = (compare_comparable tk value k))
  //			 then fail (Duplicate_map_keys (loc, expr))
  //			 else fail (Unordered_map_keys (loc, expr))
  //		       else return ()
  //		   | None -> return ()
  //		  end >>=? fun () ->
  //		  return (Some k, map_update k (Some v) map)
  //	      | Prim (loc, "Item", l, _) ->
  //		  fail @@ Invalid_arity (loc, "Item", 2, List.length l)
  //	      | Prim (loc, name, _, _) ->
  //		  fail @@ Invalid_primitive (loc, [ "Item" ], name)
  //	      | Int _ | String _ | Seq _ ->
  //		  fail (error ()))
  //	   (None, empty_map tk) vs) >>|? snd |> traced
  // | Map_t _, expr ->
  //	 traced (fail (unexpected expr [] Constant_namespace [ "Map" ]))

  | t,e -> fail (Unimplemented ("expr_to_data: "^(ScriptRepr.expr_to_string e)^" on type "^(Tezos.Definitions.string_of_ty t)^"\n"))

type judgement =
 | Typed      : stack_ty -> judgement
 | Failed     : judgement

val merge_judgements: judgement -> judgement -> tzresult judgement
let merge_judgements j1 j2 =
  match j1, j2 with
  | Typed st1, Typed st2 -> if st1 = st2 then return (Typed st1) else fail (GenericError "Untypeable")
  | Typed st,  Failed    -> return (Typed st)
  | Failed,    Typed st  -> return (Typed st)
  | Failed,    Failed    -> return Failed

val expr_to_instr : context -> expr -> stack_ty -> tzresult (uinstr*judgement)
val expr_to_instr_list : context -> list expr -> stack_ty ->
                         tzresult (uinstr*judgement)


// (* TODO: check that Sequences of instructions are parsed in this order, could have an impact on serialization *)
let rec expr_to_instr_list ctxt le sty = match le with
  | [] -> fail (GenericError "Empty list not accepted by expr_to_instr_list")
  | [c] -> (expr_to_instr ctxt c sty)
  | hd::tl ->
    res1 <-- expr_to_instr ctxt hd sty;
    let (reshd,sty1) = res1 in
    begin
      match sty1 with
      | Failed -> fail (GenericError "failure in non-tail position")
      | Typed sty1 ->
        res2 <-- expr_to_instr_list ctxt tl sty1;
        let restl,sty2 = res2 in
        return ((Seq reshd restl),sty2)
    end

and expr_to_instr ctxt e sty =
  match e, sty with
  (* stack ops *)
  | Prim "DROP" [], Item_t _ rest ->
    return (Drop,Typed rest)

  | Prim "DUP" [], Item_t a b  ->
    return (Dup,Typed (Item_t a (Item_t a b)))

  | Prim "SWAP" [],Item_t a (Item_t b c)  ->
    return (Swap,Typed (Item_t b (Item_t a c)))

  | Prim "PUSH" [ t1 ; d ], rest ->
    t <-- expr_to_ty t1;
    v <-- expr_to_data ctxt t d;
    if A.check_type ctxt v t then
    begin
      match v with
      | DInt i -> return (Const_int i, Typed (Item_t Int_t rest))
      | Nat i -> return (Const_nat i, Typed (Item_t Nat_t rest))
      | DTez i -> return (Const_tez i, Typed (Item_t Tez_t rest))
      | DBool b -> return (Const_bool b, Typed (Item_t Bool_t rest))
      | DUnit -> return (Const_unit, Typed (Item_t Unit_t rest))
      | DString s -> return (Const_string s, Typed (Item_t String_t rest))
      | _ -> fail (GenericError "Datatype not handled in expr_to_instr")
    end
    else
      fail (GenericError ("ill-typed value in expr_to_instr: "^(expr_to_string d)^" of type "^(expr_to_string t1)))

  | Prim "UNIT" [],rest ->
    return (Const_unit,Typed (Item_t Unit_t rest))

  (* options *)
  | Prim "SOME" [], Item_t t rest ->
    return (Cons_some, Typed (Item_t (Option_t t) rest))

  | Prim "NONE" [ t ], stack ->
    t <-- expr_to_ty t;
    return (Cons_none t, Typed (Item_t (Option_t t) stack))

  | Prim "IF_NONE" [ bt ; bf ], Item_t (Option_t t) rest ->
    //check_kind [ Seq_kind ] bt >>=? fun () ->
    //check_kind [ Seq_kind ] bf >>=? fun () ->
    btr <-- expr_to_instr ctxt bt rest;
    bfr <-- expr_to_instr ctxt bf (Item_t t rest);
    let bt, j1 = btr in
    let bf, j2 = bfr in
    jdgmt <-- merge_judgements j1 j2;
    return (If_none bt bf, jdgmt) // TODO: This is incorrect, there should be a merge_branches mechanisme here

  (* pairs *)
  | Prim "PAIR" [],Item_t a (Item_t b c) -> return (Cons_pair,Typed (Item_t (Pair_t a b) c))

  | Prim "CAR" [],Item_t (Pair_t a b) c  -> return (Car,Typed (Item_t a c))

  | Prim "CDR" [],Item_t (Pair_t a b) c  -> return (Cdr,Typed (Item_t b c))
  // (* unions *)
  // | Prim("LEFT", [ tr ]),
  //   Item_t (tl, rest) ->
  //     (Lwt.return (parse_ty tr)) >>=? fun (Ex_ty tr) ->
  //     return (typed loc annot (Left, Item_t (Union_t (tl, tr), rest)))
  // | Prim("RIGHT", [ tl ]),
  //   Item_t (tr, rest) ->
  //     (Lwt.return (parse_ty tl)) >>=? fun (Ex_ty tl) ->
  //     return (typed loc annot (Right, Item_t (Union_t (tl, tr), rest)))
  // | Prim("IF_LEFT", [ bt ; bf ]),
  //   (Item_t (Union_t (tl, tr), rest) as bef) ->
  //     check_kind [ Seq_kind ] bt >>=? fun () ->
  //     check_kind [ Seq_kind ] bf >>=? fun () ->
  //     parse_instr ?storage_type ?type_logger ctxt bt (Item_t (tl, rest)) >>=? fun btr ->
  //     parse_instr ?storage_type ?type_logger ctxt bf (Item_t (tr, rest)) >>=? fun bfr ->
  //     let branch ibt ibf =
  //       { loc ; instr = If_left (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
  //     merge_branches loc btr bfr { branch }

  (* lists *)
  | Prim "NIL" [ t ], rest ->
    t <-- expr_to_ty t;
    return (Nill t,Typed (Item_t (List_t t) rest))

  | Prim "CONS" [],Item_t tv (Item_t (List_t t) rest) ->
    if tv = t then return (Cons_list,Typed (Item_t (List_t t) rest))
    else fail (GenericError "Incompatible types for Cons_list")

  // | Prim("IF_CONS", [ bt ; bf ]),
  //   (Item_t (List_t t, rest) as bef) ->
  //     check_kind [ Seq_kind ] bt >>=? fun () ->
  //     check_kind [ Seq_kind ] bf >>=? fun () ->
  //     parse_instr ?storage_type ?type_logger ctxt bt (Item_t (t, Item_t (List_t t, rest))) >>=? fun btr ->
  //     parse_instr ?storage_type ?type_logger ctxt bf rest >>=? fun bfr ->
  //     let branch ibt ibf =
  //       { loc ; instr = If_cons (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
  //     merge_branches loc btr bfr { branch }

  | Prim "MAP" [],
    Item_t (Lambda_t param ret)
      (Item_t (List_t elt) rest) ->
    if param = elt then
      return (List_map, Typed (Item_t (List_t ret) rest))
    else
      fail Reject

  | Prim "REDUCE" [],
    Item_t (Lambda_t (Pair_t pelt pr) r)
      (Item_t (List_t elt) (Item_t init rest)) ->
    if r = pr && elt = pelt && init = r then
      return (List_reduce, Typed (Item_t r rest))
    else
      fail Reject

  // (* sets *)
  // | Prim("EMPTY_SET", [ t ]),
  //   rest ->
  //     (Lwt.return (parse_comparable_ty t)) >>=? fun (Ex_comparable_ty t) ->
  //     return (typed loc annot (Empty_set t, Item_t (Set_t t, rest)))
  // | Prim("MAP", []),
  //   Item_t (Lambda_t (param, ret), Item_t (Set_t elt, rest)) ->
  //     let elt = ty_of_comparable_ty elt in
  //     (Lwt.return (comparable_ty_of_ty loc ret)) >>=? fun ret ->
  //     check_item_ty elt param loc "MAP" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Set_map ret, Item_t (Set_t ret, rest)))
  // | Prim("REDUCE", []),
  //   Item_t (Lambda_t (Pair_t (pelt, pr), r),
  //           Item_t (Set_t elt, Item_t (init, rest))) ->
  //     let elt = ty_of_comparable_ty elt in
  //     check_item_ty r pr loc "REDUCE" 1 3 >>=? fun (Eq _) ->
  //     check_item_ty elt pelt loc "REDUCE" 2 3 >>=? fun (Eq _) ->
  //     check_item_ty init r loc "REDUCE" 3 3 >>=? fun (Eq _) ->
  //     return (typed loc annot (Set_reduce, Item_t (r, rest)))
  // | Prim("MEM", []),
  //   Item_t (v, Item_t (Set_t elt, rest)) ->
  //     let elt = ty_of_comparable_ty elt in
  //     check_item_ty elt v loc "MEM" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Set_mem, Item_t (Bool_t, rest)))
  // | Prim("UPDATE", []),
  //   Item_t (v, Item_t (Bool_t, Item_t (Set_t elt, rest))) ->
  //     let ty = ty_of_comparable_ty elt in
  //     check_item_ty ty v loc "UPDATE" 1 3 >>=? fun (Eq _) ->
  //     return (typed loc annot (Set_update, Item_t (Set_t elt, rest)))
  // | Prim("SIZE", []),
  //   Item_t (Set_t _, rest) ->
  //     return (typed loc annot (Set_size, Item_t (Nat_t, rest)))
  // (* maps *)
  // | Prim("EMPTY_MAP", [ tk ; tv ]),
  //   stack ->
  //     (Lwt.return (parse_comparable_ty tk)) >>=? fun (Ex_comparable_ty tk) ->
  //     (Lwt.return (parse_ty tv)) >>=? fun (Ex_ty tv) ->
  //     return (typed loc annot (Empty_map (tk, tv), Item_t (Map_t (tk, tv), stack)))
  // | Prim("MAP", []),
  //   Item_t (Lambda_t (Pair_t (pk, pv), ret), Item_t (Map_t (ck, v), rest)) ->
  //     let k = ty_of_comparable_ty ck in
  //     check_item_ty pk k loc "MAP" 1 2 >>=? fun (Eq _) ->
  //     check_item_ty pv v loc "MAP" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Map_map, Item_t (Map_t (ck, ret), rest)))
  // | Prim("REDUCE", []),
  //   Item_t (Lambda_t (Pair_t (Pair_t (pk, pv), pr), r),
  //           Item_t (Map_t (ck, v), Item_t (init, rest))) ->
  //     let k = ty_of_comparable_ty ck in
  //     check_item_ty pk k loc "REDUCE" 2 3 >>=? fun (Eq _) ->
  //     check_item_ty pv v loc "REDUCE" 2 3 >>=? fun (Eq _) ->
  //     check_item_ty r pr loc "REDUCE" 1 3 >>=? fun (Eq _) ->
  //     check_item_ty init r loc "REDUCE" 3 3 >>=? fun (Eq _) ->
  //     return (typed loc annot (Map_reduce, Item_t (r, rest)))
  // | Prim("MEM", []),
  //   Item_t (vk, Item_t (Map_t (ck, _), rest)) ->
  //     let k = ty_of_comparable_ty ck in
  //     check_item_ty vk k loc "MEM" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Map_mem, Item_t (Bool_t, rest)))
  // | Prim("GET", []),
  //   Item_t (vk, Item_t (Map_t (ck, elt), rest)) ->
  //     let k = ty_of_comparable_ty ck in
  //     check_item_ty vk k loc "GET" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Map_get, Item_t (Option_t elt, rest)))
  // | Prim("UPDATE", []),
  //   Item_t (vk, Item_t (Option_t vv, Item_t (Map_t (ck, v), rest))) ->
  //     let k = ty_of_comparable_ty ck in
  //     check_item_ty vk k loc "UPDATE" 1 3 >>=? fun (Eq _) ->
  //     check_item_ty vv v loc "UPDATE" 2 3 >>=? fun (Eq _) ->
  //     return (typed loc annot (Map_update, Item_t (Map_t (ck, v), rest)))
  // | Prim("SIZE", []),
  //   Item_t (Map_t (_, _), rest) ->
  //     return (typed loc annot (Map_size, Item_t (Nat_t, rest)))
  // (* control *)
  | Tezos.ScriptRepr.Seq [],stack -> return (Nop,Typed stack)
  | Tezos.ScriptRepr.Seq [ single ],stack ->
      expr_to_instr ctxt single stack
  // | Seq (loc, [ single ], (Some _ as annot)),
  //   stack ->
  //     parse_instr ?storage_type ?type_logger ctxt single stack >>=? begin function
  //       | Typed ({ aft } as instr) ->
  //           let nop = { bef = aft ; loc = loc ; aft ; annot = None ; instr = Nop } in
  //           return (typed loc annot (Seq (instr, nop), aft))
  //       | Failed { descr } ->
  //           let descr aft =
  //             let nop = { bef = aft ; loc = loc ; aft ; annot = None ; instr = Nop } in
  //             let descr = descr aft in
  //             { descr with instr = Seq (descr, nop) ; annot } in
  //           return (Failed { descr })
  //     end
  | Tezos.ScriptRepr.Seq (hd :: tl),stack ->
    expr_to_instr_list ctxt (hd::tl) stack
  //   stack ->
  //     parse_instr ?storage_type ?type_logger ctxt hd stack >>=? begin function
  //       | Failed _ ->
  //           fail (Fail_not_in_tail_position loc)
  //       | Typed ({ aft = middle } as ihd) ->
  //           parse_instr ?storage_type ?type_logger ctxt (Seq (loc, tl)) middle >>=? function
  //           | Failed { descr } ->
  //               let descr ret =
  //                 { loc ; instr = Seq (ihd, descr ret) ;
  //                   bef = stack ; aft = ret ; annot = None } in
  //               return (Failed { descr })
  //           | Typed itl ->
  //               return (typed loc annot (Seq (ihd, itl), itl.aft))
  //     end

  | Prim "IF" [ bt ; bf ], Item_t Bool_t rest ->
    btr <-- expr_to_instr ctxt bt rest;
    bfr <-- expr_to_instr ctxt bf rest;
    let bt, j1 = btr in
    let bf, j2 = bfr in
    jdgmt <-- merge_judgements j1 j2;
    return (If bt bf, jdgmt) // TODO: This is incorrect, there should be a merge_branches mechanisme here
      // parse_instr ?storage_type ?type_logger ctxt bt rest >>=? fun btr ->
      // parse_instr ?storage_type ?type_logger ctxt bf rest >>=? fun bfr ->
      // let branch ibt ibf =
      //   { loc ; instr = If (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
      // merge_branches loc btr bfr { branch }

  | Prim "LOOP" [ body ], Item_t Bool_t rest ->
    res <-- expr_to_instr ctxt body rest;
    let ibody, _ = res in
    return (Loop ibody, Typed rest)

  | Prim "LAMBDA" [ arg ; ret ; code ], st ->
    arg <-- expr_to_ty arg;
    ret <-- expr_to_ty ret;
    // check_kind [ Seq_kind ] code >>=? fun () ->
    res <-- expr_to_instr ctxt code (Item_t arg Empty_t);
    begin
    match res with
    | lambda, Typed (Item_t ret' Empty_t) ->
      if ret = ret' then
        return (Lambda (Lam arg ret lambda code), 
                Typed (Item_t (Lambda_t arg ret) st))
      else
        fail Reject
    | _ -> fail Reject
    end

  // | Prim("EXEC", []),
  //   Item_t (arg, Item_t (Lambda_t (param, ret), rest)) ->
  //     check_item_ty arg param loc "EXEC" 1 2 >>=? fun (Eq _) ->
  //     return (typed loc annot (Exec, Item_t (ret, rest)))

  | Prim "DIP" [ code ],Item_t v rest ->
    // check_kind [ Seq_kind ] code >>=? fun () ->
    res <-- expr_to_instr ctxt code rest;
    begin
    match res with
    | ui, Typed sty' -> return (Dip ui, Typed (Item_t v sty'))
    | ui, _ -> return (Dip ui,Failed) end

  | Prim "FAIL" [], bef ->
    return (Fail, Failed)

  // (* timestamp operations *)
  // | Prim("ADD", []),
  //   Item_t (Timestamp_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Add_timestamp_to_seconds, Item_t (Timestamp_t, rest)))
  // | Prim("ADD", []),
  //   Item_t (Nat_t, Item_t (Timestamp_t, rest)) ->
  //     return (typed loc annot (Add_seconds_to_timestamp, Item_t (Timestamp_t, rest)))

  // (* string operations *)
  | Prim "CONCAT" [], Item_t String_t (Item_t String_t rest) ->
    return (Concat, Typed (Item_t String_t rest))

  // (* currency operations *)
  // | Prim("ADD", []),
  //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
  //     return (typed loc annot (Add_tez, Item_t (Tez_t, rest)))
  // | Prim("SUB", []),
  //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
  //     return (typed loc annot (Sub_tez, Item_t (Tez_t, rest)))
  // | Prim("MUL", []),
  //   Item_t (Tez_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Mul_teznat, Item_t (Tez_t, rest)))
  // | Prim("MUL", []),
  //   Item_t (Nat_t, Item_t (Tez_t, rest)) ->
  //     return (typed loc annot (Mul_nattez, Item_t (Tez_t, rest)))

  (* boolean operations *)
  | Prim "OR" [], Item_t Bool_t (Item_t Bool_t rest) ->
    return (Or, Typed (Item_t Bool_t rest))

  | Prim "AND" [], Item_t Bool_t (Item_t Bool_t rest) ->
    return (And, Typed (Item_t Bool_t rest))

  | Prim "XOR" [], Item_t Bool_t (Item_t Bool_t rest) ->
    return (Xor, Typed (Item_t Bool_t rest))

  | Prim "NOT" [], Item_t Bool_t rest ->
    return (Not, Typed (Item_t Bool_t rest))

  (* integer operations *)
  | Prim "ABS" [], Item_t Int_t rest ->
    return (Abs_int, Typed (Item_t Nat_t rest))

  // | Prim("INT", []),
  //   Item_t (Nat_t, rest) ->
  //     return (typed loc annot (Int_nat, Item_t (Int_t, rest)))
  // | Prim("NEG", []),
  //   Item_t (Int_t, rest) ->
  //     return (typed loc annot (Neg_int, Item_t (Int_t, rest)))
  // | Prim("NEG", []),
  //   Item_t (Nat_t, rest) ->
  //     return (typed loc annot (Neg_nat, Item_t (Int_t, rest)))
  // | Prim("ADD", []),
  //   Item_t (Int_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Add_intint, Item_t (Int_t, rest)))
  // | Prim("ADD", []),
  //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Add_intnat, Item_t (Int_t, rest)))
  // | Prim("ADD", []),
  //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Add_natint, Item_t (Int_t, rest)))
  // | Prim("ADD", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Add_natnat, Item_t (Nat_t, rest)))
  | Prim "SUB" [],
    Item_t Int_t (Item_t Int_t rest) ->
      return (Sub_int, Typed (Item_t Int_t rest))
  | Prim "SUB" [],
    Item_t Int_t (Item_t Nat_t rest) ->
      return (Sub_int, Typed (Item_t Int_t rest))
  | Prim "SUB" [],
    Item_t Nat_t (Item_t Int_t rest) ->
      return (Sub_int, Typed (Item_t Int_t rest))
  | Prim "SUB" [],
    Item_t Nat_t (Item_t Nat_t rest) ->
      return (Sub_int, Typed (Item_t Int_t rest))
  // | Prim("MUL", []),
  //   Item_t (Int_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Mul_intint, Item_t (Int_t, rest)))
  // | Prim("MUL", []),
  //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Mul_intnat, Item_t (Int_t, rest)))
  // | Prim("MUL", []),
  //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Mul_natint, Item_t (Int_t, rest)))
  // | Prim("MUL", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Mul_natnat, Item_t (Nat_t, rest)))
  // | Prim("EDIV", []),
  //   Item_t (Tez_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Ediv_teznat,
  //            Item_t (Option_t (Pair_t (Tez_t,Tez_t)), rest)))
  // | Prim("EDIV", []),
  //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
  //     return (typed loc annot (Ediv_tez,
  //            Item_t (Option_t (Pair_t (Nat_t,Tez_t)), rest)))
  // | Prim("EDIV", []),
  //   Item_t (Int_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Ediv_intint,
  //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
  // | Prim("EDIV", []),
  //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Ediv_intnat,
  //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
  // | Prim("EDIV", []),
  //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
  //     return (typed loc annot (Ediv_natint,
  //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
  // | Prim("EDIV", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Ediv_natnat,
  //            Item_t (Option_t (Pair_t (Nat_t,Nat_t)), rest)))
  // | Prim("LSL", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Lsl_nat, Item_t (Nat_t, rest)))
  // | Prim("LSR", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Lsr_nat, Item_t (Nat_t, rest)))
  // | Prim("OR", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Or_nat, Item_t (Nat_t, rest)))
  // | Prim("AND", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (And_nat, Item_t (Nat_t, rest)))
  // | Prim("XOR", []),
  //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
  //     return (typed loc annot (Xor_nat, Item_t (Nat_t, rest)))
  // | Prim("NOT", []),
  //   Item_t (Int_t, rest) ->
  //     return (typed loc annot (Not_int, Item_t (Int_t, rest)))
  // | Prim("NOT", []),
  //   Item_t (Nat_t, rest) ->
  //     return (typed loc annot (Not_nat, Item_t (Int_t, rest)))

  (* comparison *)
  | Prim "COMPARE" [], Item_t Int_t (Item_t Int_t rest) ->
    return (Compare Int_key, Typed (Item_t Int_t rest))

  | Prim "COMPARE" [], Item_t Nat_t (Item_t Nat_t rest) ->
    return (Compare Nat_key, Typed (Item_t Int_t rest))

  // | Prim("COMPARE", []),
  //   Item_t (Bool_t, Item_t (Bool_t, rest)) ->
  //     return (typed loc annot (Compare Bool_key, Item_t (Int_t, rest)))
  // | Prim("COMPARE", []),
  //   Item_t (String_t, Item_t (String_t, rest)) ->
  //     return (typed loc annot (Compare String_key, Item_t (Int_t, rest)))
  // | Prim("COMPARE", []),
  //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
  //     return (typed loc annot (Compare Tez_key, Item_t (Int_t, rest)))
  // | Prim("COMPARE", []),
  //   Item_t (Key_hash_t, Item_t (Key_hash_t, rest)) ->
  //     return (typed loc annot (Compare Key_hash_key, Item_t (Int_t, rest)))
  // | Prim("COMPARE", []),
  //   Item_t (Timestamp_t, Item_t (Timestamp_t, rest)) ->
  //     return (typed loc annot (Compare Timestamp_key, Item_t (Int_t, rest)))

  (* comparators *)
  | Prim "EQ" [], Item_t Int_t rest ->
    return (Eq, Typed (Item_t Bool_t rest))

  | Prim "NEQ" [], Item_t Int_t rest ->
    return (Neq,Typed (Item_t Bool_t rest))

  | Prim "LT" [], Item_t Int_t rest ->
    return (Lt, Typed (Item_t Bool_t rest))

  | Prim "GT" [], Item_t Int_t rest ->
    return (Gt, Typed (Item_t Bool_t rest))

  | Prim "LE" [], Item_t Int_t rest ->
    return (Le, Typed (Item_t Bool_t rest))

  | Prim "GE" [], Item_t Int_t rest ->
    return (Ge, Typed (Item_t Bool_t rest))

  // (* protocol *)
  // | Prim("MANAGER", []),
  //   Item_t (Contract_t _, rest) ->
  //     return (typed loc annot (Manager, Item_t (Key_hash_t, rest)))
  // | Prim("TRANSFER_TOKENS", []),
  //   Item_t (p, Item_t
  //             (Tez_t, Item_t
  //                (Contract_t (cp, cr), Item_t
  //                   (storage, Empty_t)))) ->
  //     check_item_ty p cp loc "TRANSFER_TOKENS" 1 4 >>=? fun (Eq _) ->
  //     begin match storage_type with
  //       | Some storage_type ->
  //           check_item_ty storage storage_type loc "TRANSFER_TOKENS" 3 4 >>=? fun (Eq _) ->
  //           return (typed loc annot (Transfer_tokens storage,
  //                              Item_t (cr, Item_t (storage, Empty_t))))
  //       | None ->
  //           fail (Transfer_in_lambda loc)
  //     end
  // | Prim("CREATE_ACCOUNT", []),
  //   Item_t
  //     (Key_hash_t, Item_t
  //        (Option_t Key_hash_t, Item_t
  //           (Bool_t, Item_t
  //              (Tez_t, rest)))) ->
  //     return (typed loc annot (Create_account,
  //                        Item_t (Contract_t (Unit_t, Unit_t), rest)))
  // | Prim("DEFAULT_ACCOUNT", []),
  //   Item_t (Key_hash_t, rest) ->
  //     return
  //       (typed loc annot (Default_account, Item_t (Contract_t (Unit_t, Unit_t), rest)))
  // | Prim("CREATE_CONTRACT", []),
  //   Item_t
  //     (Key_hash_t, Item_t
  //        (Option_t Key_hash_t, Item_t
  //           (Bool_t, Item_t
  //              (Bool_t, Item_t
  //                 (Tez_t, Item_t
  //                    (Lambda_t (Pair_t (p, gp),
  //                               Pair_t (r, gr)), Item_t
  //                       (ginit, rest))))))) ->
  //     check_item_ty gp gr loc "CREATE_CONTRACT" 5 7 >>=? fun (Eq _) ->
  //     check_item_ty ginit gp loc "CREATE_CONTRACT" 6 7 >>=? fun (Eq _) ->
  //     return (typed loc annot (Create_contract (gp, p, r),
  //                        Item_t (Contract_t (p, r), rest)))
  // | Prim("NOW", []),
  //   stack ->
  //     return (typed loc annot (Now, Item_t (Timestamp_t, stack)))
  // | Prim("AMOUNT", []),
  //   stack ->
  //     return (typed loc annot (Amount, Item_t (Tez_t, stack)))
  | Prim "BALANCE" [], stack ->
    return (Balance, Typed (Item_t Tez_t stack))

  | Prim "HASH_KEY" [], Item_t Key_t rest ->
    return (Hash_key, Typed (Item_t Key_hash_t rest))

  | Prim "CHECK_SIGNATURE" [], Item_t Key_t (Item_t (Pair_t Signature_t String_t) rest) ->
    return (Check_signature, Typed (Item_t Bool_t rest))

  | Prim "H" [], Item_t t rest ->
    return (H t , Typed (Item_t String_t rest))

  // | Prim("STEPS_TO_QUOTA", []),
  //   stack ->
  //     return (typed loc annot (Steps_to_quota, Item_t (Nat_t, stack)))
  // | Prim("SOURCE", [ ta; tb ]),
  //   stack ->
  //     (Lwt.return (parse_ty ta)) >>=? fun (Ex_ty ta) ->
  //     (Lwt.return (parse_ty tb)) >>=? fun (Ex_ty tb) ->
  //     return (typed loc annot (Source (ta, tb), Item_t (Contract_t (ta, tb), stack)))
  // (* Primitive parsing errors *)
  // | Prim(("DROP" | "DUP" | "SWAP" | "SOME" | "UNIT"
  //              | "PAIR" | "CAR" | "CDR" | "CONS"
  //              | "MEM" | "UPDATE" | "MAP" | "REDUCE"
  //              | "GET" | "EXEC" | "FAIL" | "SIZE"
  //              | "CONCAT" | "ADD" | "SUB"
  //              | "MUL" | "EDIV" | "OR" | "AND" | "XOR"
  //              | "NOT"
  //              | "ABS" | "NEG" | "LSL" | "LSR"
  //              | "COMPARE" | "EQ" | "NEQ"
  //              | "LT" | "GT" | "LE" | "GE"
  //              | "MANAGER" | "TRANSFER_TOKENS" | "CREATE_ACCOUNT"
  //              | "CREATE_CONTRACT" | "NOW"
  //              | "DEFAULT_ACCOUNT" | "AMOUNT" | "BALANCE"
  //              | "CHECK_SIGNATURE" | "HASH_KEY"
  //              | "H" | "STEPS_TO_QUOTA"
  //              as name), (_ :: _ as l), _), _ ->
  //     fail (Invalid_arity (loc, name, 0, List.length l))
  // | Prim(("NONE" | "LEFT" | "RIGHT" | "NIL"
  //              | "EMPTY_SET" | "DIP" | "LOOP"
  //              as name), ([]
  //                        | _ :: _ :: _ as l), _), _ ->
  //     fail (Invalid_arity (loc, name, 1, List.length l))
  // | Prim(("PUSH" | "IF_NONE" | "IF_LEFT" | "IF_CONS"
  //              | "EMPTY_MAP" | "IF" | "SOURCE"
  //              as name), ([] | [ _ ]
  //                        | _ :: _ :: _ :: _ as l), _), _ ->
  //     fail (Invalid_arity (loc, name, 2, List.length l))
  // | Prim("LAMBDA", ([] | [ _ ] | [ _ ; _ ]
  //                        | _ :: _ :: _ :: _ :: _ as l), _), _ ->
  //     fail (Invalid_arity (loc, "LAMBDA", 3, List.length l))
  // (* Stack errors *)
  // | Prim(("ADD" | "SUB" | "MUL" | "EDIV"
  //              | "AND" | "OR" | "XOR" | "LSL" | "LSR"
  //              | "CONCAT" | "COMPARE" as name), [], _),
  //   Item_t (ta, Item_t (tb, _)) ->
  //     fail (Undefined_binop (loc, name, ta, tb))
  // | Prim(("NEG" | "ABS" | "NOT"
  //              | "EQ" | "NEQ" | "LT" | "GT" | "LE" | "GE" as name),
  //         [], _),
  //   Item_t (t, _) ->
  //     fail (Undefined_unop (loc, name, t))
  // | Prim(("REDUCE" | "UPDATE" as name), [], _),
  //   stack ->
  //     fail (Bad_stack (loc, name, 3, stack))
  // | Prim("CREATE_CONTRACT", [], _),
  //   stack ->
  //     fail (Bad_stack (loc, "CREATE_CONTRACT", 7, stack))
  // | Prim("CREATE_ACCOUNT", [], _),
  //   stack ->
  //     fail (Bad_stack (loc, "CREATE_ACCOUNT", 4, stack))
  // | Prim("TRANSFER_TOKENS", [], _),
  //   stack ->
  //     fail (Bad_stack (loc, "TRANSFER_TOKENS", 3, stack))
  // | Prim(("DROP" | "DUP" | "CAR" | "CDR" | "SOME" | "H" | "DIP"
  //              | "IF_NONE" | "LEFT" | "RIGHT" | "IF_LEFT" | "IF"
  //              | "LOOP" | "IF_CONS" | "MANAGER" | "DEFAULT_ACCOUNT"
  //              | "NEG" | "ABS" | "INT" | "NOT"
  //              | "EQ" | "NEQ" | "LT" | "GT" | "LE" | "GE" as name), _, _),
  //   stack ->
  //     fail (Bad_stack (loc, name, 1, stack))
  // | Prim(("SWAP" | "PAIR" | "CONS"
  //              | "MAP" | "GET" | "MEM" | "EXEC"
  //              | "CHECK_SIGNATURE" | "ADD" | "SUB" | "MUL"
  //              | "EDIV" | "AND" | "OR" | "XOR"
  //              | "LSL" | "LSR" | "CONCAT" as name), _, _),
  //   stack ->
  //     fail (Bad_stack (loc, name, 2, stack))
  // (* Generic parsing errors *)
  // | expr, _ ->
  //     fail @@ unexpected expr [ Seq_kind ] Instr_namespace
  //       [ "DROP" ; "DUP" ; "SWAP" ; "SOME" ; "UNIT" ;
  //         "PAIR" ; "CAR" ; "CDR" ; "CONS" ;
  //         "MEM" ; "UPDATE" ; "MAP" ; "REDUCE" ;
  //         "GET" ; "EXEC" ; "FAIL" ; "SIZE" ;
  //         "CONCAT" ; "ADD" ; "SUB" ;
  //         "MUL" ; "EDIV" ; "OR" ; "AND" ; "XOR" ;
  //         "NOT" ;
  //         "ABS" ; "INT"; "NEG" ; "LSL" ; "LSR" ;
  //         "COMPARE" ; "EQ" ; "NEQ" ;
  //         "LT" ; "GT" ; "LE" ; "GE" ;
  //         "MANAGER" ; "TRANSFER_TOKENS" ; "CREATE_ACCOUNT" ;
  //         "CREATE_CONTRACT" ; "NOW" ; "AMOUNT" ; "BALANCE" ;
  //         "DEFAULT_ACCOUNT" ; "CHECK_SIGNATURE" ; "H" ; "HASH_KEY" ;
  //         "STEPS_TO_QUOTA" ;
  //         "PUSH" ; "NONE" ; "LEFT" ; "RIGHT" ; "NIL" ;
  //         "EMPTY_SET" ; "DIP" ; "LOOP" ;
  //         "IF_NONE" ; "IF_LEFT" ; "IF_CONS" ;
  //         "EMPTY_MAP" ; "IF" ; "SOURCE" ; "LAMBDA" ]
  | e, _ -> fail (Unimplemented ("expr_to_instr: " ^ (ScriptRepr.expr_to_string e)))
