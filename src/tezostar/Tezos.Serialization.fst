module Tezos.Serialization

open Tezos.Primitives
module D = Tezos.Definitions
open D

open Tezos.UntypedDefinitions
open Tezos.TezRepr
module S = Tezos.ScriptRepr
open S

open Tezos.Storage
open Tezos.Error

// type code =
//   { code : expr ;
//     arg_type : expr ;
//     ret_type : expr ;
//     storage_type : expr }

// type storage =
//   { storage : expr ;
//     storage_type : expr }

// type t =
//   { code : code ;
//     storage : storage }

val unparse_comparable_ty : t : comparable_ty -> expr

let unparse_comparable_ty t = match t with
  | Int_key -> Prim "int" []
  | Nat_key -> Prim "nat" []
  | String_key -> Prim "string" []
  | Tez_key -> Prim "tez" []
  | Bool_key -> Prim "bool" []
  | Key_hash_key -> Prim "key_hash" []
  | Timestamp_key -> Prim "timestamp" []

val unparse_ty : t : ty -> Tot expr (decreases t)
#set-options "--z3rlimit 50 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 1"


let rec unparse_ty (t : ty) : expr = match t with
  | Unit_t -> Prim "unit" []
  | Int_t -> Prim "int" []
  | Nat_t -> Prim "nat" []
  | String_t -> Prim "string" []
  | Tez_t -> Prim "tez" []
  | Bool_t -> Prim "bool" []
  | Key_hash_t -> Prim "key_hash" []
  | Key_t -> Prim "key" []
  | Timestamp_t -> Prim "timestamp" []
  | Signature_t -> Prim "signature" []
  | Contract_t utl utr ->
      let tl = unparse_ty utl in
      let tr = unparse_ty utr in
      Prim "contract" [ tl; tr ]
  | Pair_t utl  utr ->
      let tl = unparse_ty utl in
      let tr = unparse_ty utr in
      Prim "pair" [ tl; tr ]
  | Union_t utl utr ->
      let tl = unparse_ty utl in
      let tr = unparse_ty utr in
      Prim "or" [ tl; tr ]
  | Lambda_t uta utr ->
      let ta = unparse_ty uta in
      let tr = unparse_ty utr in
      Prim "lambda" [ ta; tr ]
  | Option_t ut ->
      let t = unparse_ty ut in
      Prim "option" [ t ]
  | List_t ut ->
      let t = unparse_ty ut in
      Prim "list" [ t ]
  | Set_t ut ->
      let t = unparse_comparable_ty ut in
      Prim "set" [ t ]
  | Map_t uta utr ->
      let ta = unparse_comparable_ty uta in
      let tr = unparse_ty utr in
      Prim "map" [ ta; tr ]


	  // Hex_encode.hex_encode
	  //   (MBytes.to_string (Data_encoding.Binary.to_bytes Ed25519.Signature.encoding s)) in
assume val hex_encode : signature -> string


// Ed25519.Public_key.to_b58check
assume val key_to_b58check : key -> string
assume val contract_to_b58check : typed_contract -> string
assume val key_hash_to_b58check : pkeyhash -> string
assume val timestamp_to_notation : timestamp -> string

let string_of_tez : tez -> string = string_of_int


val unparse_data : (t : ty) -> (a : tagged_data) -> expr
// val unparse_instr :

let rec unparse_data = fun ty a -> match ty, a with
    | Unit_t, DUnit ->
	Prim  "Unit" []
    | Int_t, DInt v ->
	Int  (string_of_int v)
    | Nat_t, DInt v ->
	Int  (string_of_int v)
    | String_t, DString s ->
	String  s
    | Bool_t, DBool true ->
	Prim  "True" []
    | Bool_t, DBool false ->
	Prim  "False" []
    | Timestamp_t, Timestamp t ->
	String  (timestamp_to_notation t)
    | Contract_t _ _, DContract c  ->
	String  (contract_to_b58check c)
    | Signature_t, DSignature s ->
	let text = hex_encode s in
	String  text
    | Tez_t, DTez v ->
	String  (string_of_tez v)
    | Key_t, DKey k ->
	String  (key_to_b58check k)
    | Key_hash_t, DKey_hash k ->
	String  (key_hash_to_b58check k)
    | Pair_t tl tr, DPair l r ->
	let l = unparse_data tl l in
	let r = unparse_data tr r in
	Prim  "Pair" [ l; r ]
    // | Union_t tl  _, Left l -> // TODO
    //     let l = unparse_data tl l in
    //     Prim  "Left" [ l ]
    // | Union_t _ tr, Right r -> // TODO
    //     let r = unparse_data tr r in
    //     Prim  "Right" [ r ]
    | Option_t t, DOption (Some v) ->
	let v = unparse_data t v in
	Prim  "Some" [ v ]
    | Option_t _, DOption None ->
	Prim  "None" []
    | List_t t, DList items ->
	let items = List.Tot.map (unparse_data t) items in
	Prim  "List" items
// the following two cases have problems with termination (calling unparse_data in a fold). One hack would be to take the structure of the map into account, but that would break the abstraction (I have done it elsewhere though..). Another would be to add some fuel and parametrize correction by it.
    // | Set_t t, DSet set ->
    //     let t' = ty_of_comp_ty t in
    //     let items =
    //       set_fold tagged_data set
    //         (fun acc item  ->
    //            unparse_data t' item :: acc )
    //         [] in
    //     Prim  "Set" (List.Tot.rev items)
    // | Map_t kt vt, DMap map ->
    //     let kt = ty_of_comp_ty kt in
    //     let items =
    //       map_fold_left tagged_data tagged_data map (fun acc k v  ->
    //           (Prim  "Item"
    //                 [ unparse_data kt k;
    //                   unparse_data vt v ])
    //           :: acc) [] // Warning: Tezos does more of a fold_right but not sure exactly what it does
    //	      in
    //     Prim  "Map" (List.Tot.rev items)
    | Lambda_t _ _, DLambda (Lam _ _ _ e) -> e

    | _ -> String "not handled yet"

// val parse_instr : expr -> (sty : stack_ty) -> uinstr

// type parsed_uinstr =
// | Success : uinstr -> stack_ty -> parsed_uinstr
// | Incorrect : expr -> parsed_uinstr


assume val int_of_string : string -> option int
assume val nat_of_string : string -> option nat
val tez_of_string : string -> option tez
let tez_of_string = nat_of_string
assume val timestamp_of_seconds : string -> option timestamp
assume val timestamp_of_notation : string -> option timestamp
assume val ed25519_public_key_of_b58check_exn : string -> option key
assume val ed25519_public_key_hash_of_b58check_exn : string -> option pkeyhash
assume val decode_signature : string -> option signature
assume val contract_of_b58check : string -> option contract

val parse_contract : context -> ty -> ty -> c:contract -> Tot (option typed_contract)
let parse_contract (ctxt : context) (targ : ty) (tret : ty) (c : contract) =
  match exists_contract ctxt c with
    | true -> begin
    match get_script ctxt c with
    | Ok (Script code storage) -> None // TODO: something
    | _ -> None
      end
    | false -> None
 // stub. There needs to be some interaction with the context


(**
 * Measure on [expr] used to prove termination of mutually-recursive
 * [parse_] functions below
 *)
val measure: expr -> nat
val measures: list expr -> nat
let rec measure = function
  | Int _     -> 0
  | String _  -> 0
  | Prim _ es -> 1 + measures es
  | Seq es    -> 1 + measures es
and measures = function
  | []        -> 0
  | e :: es'   -> 1 + measure e + measures es'

(** The second decreasing argument orders recursive calls that don't decrease [measure] *)
val parse_data  : context -> ty -> e:expr -> Tot (option tagged_data)
  (decreases %[measure e; 2])
val parse_lambda: context -> ty -> ty -> e:expr -> Tot (option (ty * ty * expr * uinstr))
  (decreases %[measure e; 1])
val parse_instr : context -> e:expr -> stack_ty -> Tot (option (uinstr * stack_ty))
  (decreases %[measure e; 0])

#set-options "--initial_fuel 3 --max_fuel 3"

let rec parse_data (ctxt : context) ty script_data =
    match ty, script_data with
    (* Unit *)
    | Unit_t, Prim "Unit" [] -> Some DUnit
    (* Booleans *)
    | Bool_t, Prim "True" [] -> Some (DBool true)
    | Bool_t, Prim "False" [] -> Some (DBool false)
    (* Strings *)
    | String_t, String v -> Some (DString v)
    (* Integers *)
    | Int_t, Int v ->
	begin match int_of_string v with
	  | None -> None
	  | Some v -> Some (DInt v)
	end
    | Nat_t, Int v ->
	begin match int_of_string v with
	  | None -> None
	  | Some v ->
	      if v >= 0 then
		Some (Nat v)
	      else None
	end
    (* Tez amounts *)
    | Tez_t, String v -> begin match (tez_of_string v) with | Some t -> Some (DTez t) | _ -> None end
    (* Timestamps *)
    | Timestamp_t, Int v -> begin
	match (timestamp_of_seconds v) with
	| Some v -> Some (Timestamp v)
	| None -> None
      end
    | Timestamp_t, String s -> begin
	  match timestamp_of_notation s with
	  | Some v -> Some (Timestamp v)
	  | None -> None end
    (* IDs *)
    | Key_t, String s ->
	begin
	    match (ed25519_public_key_of_b58check_exn s) with
	    | Some k -> Some (DKey k)
	    | _ -> None
	end
    | Key_hash_t, String s ->
	begin
	    match (ed25519_public_key_hash_of_b58check_exn s) with
	    | Some kh -> Some (DKey_hash kh)
	    | _ -> None
	end
    (* Signatures *)
    | Signature_t, String s -> begin
	  match decode_signature s with
	  | Some s -> Some (DSignature s)
	  | None -> None
      end
    (* Contracts *)
    | Contract_t targ tret, String s -> begin
      match contract_of_b58check s with
	| Some c -> begin match parse_contract ctxt targ tret c with
	   | Some (tc : typed_contract) -> Some (DContract tc)
	   | None -> None end
	| None -> None end   // | Contract_t _, expr ->
    //     traced (fail (Invalid_kind (location expr, [ String_kind ], kind expr)))
    (* Pairs *)
    | Pair_t ta tb, Prim "Pair" [ va; vb ] -> begin
      match (parse_data ctxt ta va,parse_data ctxt tb vb) with
      | (Some va, Some vb) -> Some (DPair va vb)
      | _ -> None end
    // (* Unions *)
    // | Union_t (tl, _), Prim (_, "Left", [ v ], _) ->
    //     traced @@
    //     parse_data ?type_logger ctxt tl v >>=? fun v ->
    //     return (L v)
    (* Lambdas *)
    | Lambda_t ta tr, S.Seq code ->
      begin
      match parse_lambda ctxt ta tr script_data with
      | Some (t1, t2, expr, ui) -> Some (DLambda (Lam t1 t2 ui expr))
      | None -> None
      end
    // (* Options *)
    | Option_t t, Prim "Some" [ v ] -> begin
	match parse_data ctxt t v with
	| Some (DOption (Some v)) -> Some (DOption (Some v))
	| _ -> None end
    | Option_t _, Prim "None" [] ->
	Some(DOption None)
    // (* Lists *)
    // | List_t t, Prim "List" vs ->
    //     List.Tot.fold_right
    //       (fun v rest ->
    //          match parse_data (f-1) ctxt t v,rest with
    //	     | Some v, Some (DList rest) -> Some (DList (v :: rest))
    //	     | _, _ -> None)
    //       vs (Some (DList []))
    // (* Sets *)
    // | Set_t t, (Prim (loc, "Set", vs, _) as expr) ->
    //     fold_left_s
    //       (fun (last_value, set) v ->
    //          parse_comparable_data ?type_logger ctxt t v >>=? fun v ->
    //          begin match last_value with
    //           | Some value ->
    //               if Compare.Int.(0 <= (compare_comparable t value v))
    //               then
    //                 if Compare.Int.(0 = (compare_comparable t value v))
    //                 then fail (Duplicate_set_values (loc, expr))
    //                 else fail (Unordered_set_values (loc, expr))
    //               else return ()
    //           | None -> return ()
    //          end >>=? fun () ->
    //          return (Some v, set_update v true set))
    //       (None, empty_set t) vs >>|? snd |> traced
    // (* Maps *)
    // | Map_t (tk, tv), (Prim (loc, "Map", vs, _) as expr) ->
    //     (fold_left_s
    //       (fun (last_value, map) -> function
    //          | Prim (_, "Item", [ k; v ], _) ->
    //              parse_comparable_data ?type_logger ctxt tk k >>=? fun k ->
    //              parse_data ?type_logger ctxt tv v >>=? fun v ->
    //              begin match last_value with
    //               | Some value ->
    //                   if Compare.Int.(0 <= (compare_comparable tk value k))
    //                   then
    //                     if Compare.Int.(0 = (compare_comparable tk value k))
    //                     then fail (Duplicate_map_keys (loc, expr))
    //                     else fail (Unordered_map_keys (loc, expr))
    //                   else return ()
    //               | None -> return ()
    //              end >>=? fun () ->
    //              return (Some k, map_update k (Some v) map)
    //          | Prim (loc, "Item", l, _) ->
    //              fail @@ Invalid_arity (loc, "Item", 2, List.length l)
    //          | Prim (loc, name, _, _) ->
    //              fail @@ Invalid_primitive (loc, [ "Item" ], name)
    //          | Int _ | String _ | Seq _ ->
    //              fail (error ()))
    //       (None, empty_map tk) vs) >>|? snd |> traced
| _, _ -> None


  // : type arg ret storage. context ->
  //   ?storage_type: storage ty ->
  //   ?type_logger: (int * (Script.expr list * Script.expr list) -> unit) ->
  //  arg ty -> ret ty -> Script.expr -> (arg, ret) lambda tzresult Lwt.t =
  // fun ctxt ?storage_type ?type_logger arg ret script_instr ->
  //   parse_instr ctxt ?storage_type ?type_logger
  //     script_instr (Item_t (arg, Empty_t)) >>=? function
  //   | Typed ({ loc ; aft = (Item_t (ty, Empty_t) as stack_ty) } as descr) ->
  //       trace
  //         (Bad_return (loc, stack_ty, ret))
  //         (Lwt.return (ty_eq ty ret)) >>=? fun (Eq _) ->
  //       return (Lam (descr, script_instr) : (arg, ret) lambda)
  //   | Typed { loc ; aft = stack_ty } ->
  //       fail (Bad_return (loc, stack_ty, ret))
  //   | Failed { descr } ->
  //       return (Lam (descr (Item_t (ret, Empty_t)), script_instr) : (arg, ret) lambda)

and parse_lambda ctxt targ tret expr =
  match parse_instr ctxt expr (stackify targ) with
  | Some(ui,sty) -> Some(targ,tret,expr, ui)
  | None -> None

and parse_instr ctxt (e : expr) (sty : stack_ty) =
     match e, sty with
    (* stack ops *)
    | Prim  "DROP" [],
      Item_t  _ rest -> Some(Drop,rest)
    | Prim  "DUP" [],
      Item_t v rest -> Some( Dup, (Item_t v (Item_t v rest)))
    | Prim  "SWAP" [],
      Item_t v (Item_t w rest) -> Some( Swap, (Item_t w (Item_t v rest)))
//     | Prim  "PUSH" [ t ; d ],
//       stack ->
//	match
//         (Lwt.return (parse_ty t)) >>=? fun (Ex_ty t) ->
//         parse_data ?type_logger ctxt t d >>=? fun v ->
//         return (typed loc annot (Const v, Item_t (t, stack)))
//     // | Prim  "UNIT" []
//     //   stack ->
//     //     return (typed loc annot (Const (), Item_t (Unit_t, stack)))
//     // (* options *)
//     // | Prim  "SOME" []
//     //   Item_t (t, rest) ->
//     //     return (typed loc annot (Cons_some, Item_t (Option_t t, rest)))
//     // | Prim  "NONE" [ t ]
//     //   stack ->
//     //     (Lwt.return (parse_ty t)) >>=? fun (Ex_ty t) ->
//     //     return (typed loc annot (Cons_none t, Item_t (Option_t t, stack)))
//     // | Prim  "IF_NONE" [ bt ; bf ]
//     //   (Item_t (Option_t t, rest) as bef) ->
//     //     check_kind [ Seq_kind ] bt >>=? fun () ->
//     //     check_kind [ Seq_kind ] bf >>=? fun () ->
//     //     parse_instr ?storage_type ?type_logger ctxt bt rest >>=? fun btr ->
//     //     parse_instr ?storage_type ?type_logger ctxt bf (Item_t (t, rest)) >>=? fun bfr ->
//     //     let branch ibt ibf =
//     //       { loc ; instr = If_none (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
//     //     merge_branches loc btr bfr { branch }
//     // (* pairs *)
    | Prim  "PAIR" [],
	Item_t a (Item_t b rest) ->
	Some(Cons_pair, Item_t (Pair_t a b) rest)
    | Prim  "CAR" [],
      Item_t (Pair_t a _) rest ->
	Some(Car, Item_t a rest)
    | Prim  "CDR" [],
      Item_t (Pair_t _ b) rest ->
	Some(Cdr, Item_t b rest)
//     // (* unions *)
//     // | Prim  "LEFT" [ tr ]
//     //   Item_t (tl, rest) ->
//     //     (Lwt.return (parse_ty tr)) >>=? fun (Ex_ty tr) ->
//     //     return (typed loc annot (Left, Item_t (Union_t (tl, tr), rest)))
//     // | Prim  "RIGHT" [ tl ]
//     //   Item_t (tr, rest) ->
//     //     (Lwt.return (parse_ty tl)) >>=? fun (Ex_ty tl) ->
//     //     return (typed loc annot (Right, Item_t (Union_t (tl, tr), rest)))
//     // | Prim  "IF_LEFT" [ bt ; bf ]
//     //   (Item_t (Union_t (tl, tr), rest) as bef) ->
//     //     check_kind [ Seq_kind ] bt >>=? fun () ->
//     //     check_kind [ Seq_kind ] bf >>=? fun () ->
//     //     parse_instr ?storage_type ?type_logger ctxt bt (Item_t (tl, rest)) >>=? fun btr ->
//     //     parse_instr ?storage_type ?type_logger ctxt bf (Item_t (tr, rest)) >>=? fun bfr ->
//     //     let branch ibt ibf =
//     //       { loc ; instr = If_left (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
//     //     merge_branches loc btr bfr { branch }
//     // (* lists *)
//     // | Prim  "NIL" [ t ]
//     //   stack ->
//     //     (Lwt.return (parse_ty t)) >>=? fun (Ex_ty t) ->
//     //     return (typed loc annot (Nil, Item_t (List_t t, stack)))
//     // | Prim  "CONS" []
//     //   Item_t (tv, Item_t (List_t t, rest)) ->
//     //     check_item_ty tv t loc "CONS" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Cons_list, Item_t (List_t t, rest)))
//     // | Prim  "IF_CONS" [ bt ; bf ]
//     //   (Item_t (List_t t, rest) as bef) ->
//     //     check_kind [ Seq_kind ] bt >>=? fun () ->
//     //     check_kind [ Seq_kind ] bf >>=? fun () ->
//     //     parse_instr ?storage_type ?type_logger ctxt bt (Item_t (t, Item_t (List_t t, rest))) >>=? fun btr ->
//     //     parse_instr ?storage_type ?type_logger ctxt bf rest >>=? fun bfr ->
//     //     let branch ibt ibf =
//     //       { loc ; instr = If_cons (ibt, ibf) ; bef ; aft = ibt.aft ; annot } in
//     //     merge_branches loc btr bfr { branch }
//     // | Prim  "MAP" []
//     //   Item_t (Lambda_t (param, ret), Item_t (List_t elt, rest)) ->
//     //     check_item_ty elt param loc "MAP" 2 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (List_map, Item_t (List_t ret, rest)))
//     // | Prim  "REDUCE" []
//     //   Item_t (Lambda_t (Pair_t (pelt, pr), r),
//     //           Item_t (List_t elt, Item_t (init, rest))) ->
//     //     check_item_ty r pr loc "REDUCE" 1 3 >>=? fun (Eq _) ->
//     //     check_item_ty elt pelt loc "REDUCE" 2 3 >>=? fun (Eq _) ->
//     //     check_item_ty init r loc "REDUCE" 3 3 >>=? fun (Eq _) ->
//     //     return (typed loc annot (List_reduce, Item_t (r, rest)))
//     // (* sets *)
//     // | Prim  "EMPTY_SET" [ t ]
//     //   rest ->
//     //     (Lwt.return (parse_comparable_ty t)) >>=? fun (Ex_comparable_ty t) ->
//     //     return (typed loc annot (Empty_set t, Item_t (Set_t t, rest)))
//     // | Prim  "MAP" []
//     //   Item_t (Lambda_t (param, ret), Item_t (Set_t elt, rest)) ->
//     //     let elt = ty_of_comparable_ty elt in
//     //     (Lwt.return (comparable_ty_of_ty loc ret)) >>=? fun ret ->
//     //     check_item_ty elt param loc "MAP" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Set_map ret, Item_t (Set_t ret, rest)))
//     // | Prim  "REDUCE" []
//     //   Item_t (Lambda_t (Pair_t (pelt, pr), r),
//     //           Item_t (Set_t elt, Item_t (init, rest))) ->
//     //     let elt = ty_of_comparable_ty elt in
//     //     check_item_ty r pr loc "REDUCE" 1 3 >>=? fun (Eq _) ->
//     //     check_item_ty elt pelt loc "REDUCE" 2 3 >>=? fun (Eq _) ->
//     //     check_item_ty init r loc "REDUCE" 3 3 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Set_reduce, Item_t (r, rest)))
//     // | Prim  "MEM" []
//     //   Item_t (v, Item_t (Set_t elt, rest)) ->
//     //     let elt = ty_of_comparable_ty elt in
//     //     check_item_ty elt v loc "MEM" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Set_mem, Item_t (Bool_t, rest)))
//     // | Prim  "UPDATE" []
//     //   Item_t (v, Item_t (Bool_t, Item_t (Set_t elt, rest))) ->
//     //     let ty = ty_of_comparable_ty elt in
//     //     check_item_ty ty v loc "UPDATE" 1 3 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Set_update, Item_t (Set_t elt, rest)))
//     // | Prim  "SIZE" []
//     //   Item_t (Set_t _, rest) ->
//     //     return (typed loc annot (Set_size, Item_t (Nat_t, rest)))
//     // (* maps *)
//     // | Prim  "EMPTY_MAP" [ tk ; tv ]
//     //   stack ->
//     //     (Lwt.return (parse_comparable_ty tk)) >>=? fun (Ex_comparable_ty tk) ->
//     //     (Lwt.return (parse_ty tv)) >>=? fun (Ex_ty tv) ->
//     //     return (typed loc annot (Empty_map (tk, tv), Item_t (Map_t (tk, tv), stack)))
//     // | Prim  "MAP" []
//     //   Item_t (Lambda_t (Pair_t (pk, pv), ret), Item_t (Map_t (ck, v), rest)) ->
//     //     let k = ty_of_comparable_ty ck in
//     //     check_item_ty pk k loc "MAP" 1 2 >>=? fun (Eq _) ->
//     //     check_item_ty pv v loc "MAP" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Map_map, Item_t (Map_t (ck, ret), rest)))
//     // | Prim  "REDUCE" []
//     //   Item_t (Lambda_t (Pair_t (Pair_t (pk, pv), pr), r),
//     //           Item_t (Map_t (ck, v), Item_t (init, rest))) ->
//     //     let k = ty_of_comparable_ty ck in
//     //     check_item_ty pk k loc "REDUCE" 2 3 >>=? fun (Eq _) ->
//     //     check_item_ty pv v loc "REDUCE" 2 3 >>=? fun (Eq _) ->
//     //     check_item_ty r pr loc "REDUCE" 1 3 >>=? fun (Eq _) ->
//     //     check_item_ty init r loc "REDUCE" 3 3 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Map_reduce, Item_t (r, rest)))
//     // | Prim  "MEM" []
//     //   Item_t (vk, Item_t (Map_t (ck, _), rest)) ->
//     //     let k = ty_of_comparable_ty ck in
//     //     check_item_ty vk k loc "MEM" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Map_mem, Item_t (Bool_t, rest)))
//     // | Prim  "GET" []
//     //   Item_t (vk, Item_t (Map_t (ck, elt), rest)) ->
//     //     let k = ty_of_comparable_ty ck in
//     //     check_item_ty vk k loc "GET" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Map_get, Item_t (Option_t elt, rest)))
//     // | Prim  "UPDATE" []
//     //   Item_t (vk, Item_t (Option_t vv, Item_t (Map_t (ck, v), rest))) ->
//     //     let k = ty_of_comparable_ty ck in
//     //     check_item_ty vk k loc "UPDATE" 1 3 >>=? fun (Eq _) ->
//     //     check_item_ty vv v loc "UPDATE" 2 3 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Map_update, Item_t (Map_t (ck, v), rest)))
//     // | Prim  "SIZE" []
//     //   Item_t (Map_t (_, _), rest) ->
//     //     return (typed loc annot (Map_size, Item_t (Nat_t, rest)))
//     // (* control *)
//     // | Seq (loc, []
//     //   stack ->
//     //     return (typed loc annot (Nop, stack))
//     // | Seq (_, [ single ] None),
//     //   stack ->
//     //     parse_instr ?storage_type ?type_logger ctxt single stack
//     // | Seq (loc, [ single ] (Some _ as annot)),
//     //   stack ->
//     //     parse_instr ?storage_type ?type_logger ctxt single stack >>=? begin function
//     //       | Typed ({ aft } as instr) ->
//     //           let nop = { bef = aft ; loc = loc ; aft ; annot = None ; instr = Nop } in
//     //           return (typed loc annot (Seq (instr, nop), aft))
//     //       | Failed { descr } ->
//     //           let descr aft =
//     //             let nop = { bef = aft ; loc = loc ; aft ; annot = None ; instr = Nop } in
//     //             let descr = descr aft in
//     //             { descr with instr = Seq (descr, nop) ; annot } in
//     //           return (Failed { descr })
//     //     end
    | S.Seq (hd :: tl),
      sty -> begin
	match parse_instr ctxt hd sty with
	| Some(ui,afty) -> parse_instr ctxt (S.Seq tl) afty
	| None -> None
	end

    | Prim  "IF" [ bt ; bf ],
      (Item_t Bool_t rest) -> begin
      match bt, bf with
	| S.Seq _,S.Seq _ -> begin
	  match parse_instr ctxt bt rest,parse_instr ctxt bf rest with
	  | (Some(ui1, sty1),Some(ui2,sty2)) -> if sty1 = sty2 then Some(If ui1 ui2, sty1) else None
	  | _ -> None
	  end
	| _ -> None
    end
    | Prim  "LOOP" [ body ],
      (Item_t Bool_t rest) -> begin
    match body with
    | S.Seq _ -> begin
      match parse_instr ctxt body rest with
	| Some(ui,afty) -> if afty = sty (*(Item_t Bool_t rest)*) then
	  Some(Loop ui, afty) else None
	| _ -> None end
    | _ -> None
    end
//     // | Prim  "LAMBDA" [ arg ; ret ; code ]
//     //   stack ->
//     //     (Lwt.return (parse_ty arg)) >>=? fun (Ex_ty arg) ->
//     //     (Lwt.return (parse_ty ret)) >>=? fun (Ex_ty ret) ->
//     //     check_kind [ Seq_kind ] code >>=? fun () ->
//     //     parse_lambda ?type_logger ctxt arg ret code >>=? fun lambda ->
//     //     return (typed loc annot (Lambda lambda, Item_t (Lambda_t (arg, ret), stack)))
//     // | Prim  "EXEC" []
//     //   Item_t (arg, Item_t (Lambda_t (param, ret), rest)) ->
//     //     check_item_ty arg param loc "EXEC" 1 2 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Exec, Item_t (ret, rest)))
    | Prim  "DIP" [ code ],
      Item_t v rest -> begin
	match code with
	| S.Seq _ -> begin match parse_instr ctxt code rest with
	  | Some(ui,afty) -> Some(Dip ui, Item_t v afty)
	  | _ -> None end
	| _ -> None end
    | Prim  "FAIL" [],
      bef -> Some(Fail,bef) (* problem here, what's the "after" stack we want? In Tezos, instead of outputting an option type, they output a "judgement" type which has a constructor Failed with a function mapping an output stack type afty to a judgement  *)
//     // (* timestamp operations *)
//     // | Prim  "ADD" []
//     //   Item_t (Timestamp_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Add_timestamp_to_seconds, Item_t (Timestamp_t, rest)))
//     // | Prim  "ADD" []
//     //   Item_t (Nat_t, Item_t (Timestamp_t, rest)) ->
//     //     return (typed loc annot (Add_seconds_to_timestamp, Item_t (Timestamp_t, rest)))
//     // (* string operations *)
//     // | Prim  "CONCAT" []
//     //   Item_t (String_t, Item_t (String_t, rest)) ->
//     //     return (typed loc annot (Concat, Item_t (String_t, rest)))
//     // (* currency operations *)
//     // | Prim  "ADD" []
//     //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
//     //     return (typed loc annot (Add_tez, Item_t (Tez_t, rest)))
//     // | Prim  "SUB" []
//     //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
//     //     return (typed loc annot (Sub_tez, Item_t (Tez_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Tez_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Mul_teznat, Item_t (Tez_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Nat_t, Item_t (Tez_t, rest)) ->
//     //     return (typed loc annot (Mul_nattez, Item_t (Tez_t, rest)))
//     // (* boolean operations *)
    | Prim  "OR" [],
      Item_t Bool_t (Item_t Bool_t rest) ->
      Some(Or, Item_t Bool_t rest)
    | Prim  "AND" [],
      Item_t Bool_t (Item_t Bool_t rest) ->
      Some(And, Item_t Bool_t rest)
//     // | Prim  "XOR" []
//     //   Item_t (Bool_t, Item_t (Bool_t, rest)) ->
//     //     return (typed loc annot (Xor, Item_t (Bool_t, rest)))
//     // | Prim  "NOT" []
//     //   Item_t (Bool_t, rest) ->
//     //     return (typed loc annot (Not, Item_t (Bool_t, rest)))
//     // (* integer operations *)
//     // | Prim  "ABS" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Abs_int, Item_t (Nat_t, rest)))
//     // | Prim  "INT" []
//     //   Item_t (Nat_t, rest) ->
//     //     return (typed loc annot (Int_nat, Item_t (Int_t, rest)))
//     // | Prim  "NEG" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Neg_int, Item_t (Int_t, rest)))
//     // | Prim  "NEG" []
//     //   Item_t (Nat_t, rest) ->
//     //     return (typed loc annot (Neg_nat, Item_t (Int_t, rest)))
//     // | Prim  "ADD" []
//     //   Item_t (Int_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Add_intint, Item_t (Int_t, rest)))
//     // | Prim  "ADD" []
//     //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Add_intnat, Item_t (Int_t, rest)))
//     // | Prim  "ADD" []
//     //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Add_natint, Item_t (Int_t, rest)))
//     // | Prim  "ADD" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Add_natnat, Item_t (Nat_t, rest)))
//     // | Prim  "SUB" []
//     //   Item_t (Int_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Sub_int, Item_t (Int_t, rest)))
//     // | Prim  "SUB" []
//     //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Sub_int, Item_t (Int_t, rest)))
//     // | Prim  "SUB" []
//     //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Sub_int, Item_t (Int_t, rest)))
//     // | Prim  "SUB" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Sub_int, Item_t (Int_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Int_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Mul_intint, Item_t (Int_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Mul_intnat, Item_t (Int_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Mul_natint, Item_t (Int_t, rest)))
//     // | Prim  "MUL" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Mul_natnat, Item_t (Nat_t, rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Tez_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Ediv_teznat,
//     //            Item_t (Option_t (Pair_t (Tez_t,Tez_t)), rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
//     //     return (typed loc annot (Ediv_tez,
//     //            Item_t (Option_t (Pair_t (Nat_t,Tez_t)), rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Int_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Ediv_intint,
//     //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Int_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Ediv_intnat,
//     //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Nat_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Ediv_natint,
//     //            Item_t (Option_t (Pair_t (Int_t,Nat_t)), rest)))
//     // | Prim  "EDIV" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Ediv_natnat,
//     //            Item_t (Option_t (Pair_t (Nat_t,Nat_t)), rest)))
//     // | Prim  "LSL" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Lsl_nat, Item_t (Nat_t, rest)))
//     // | Prim  "LSR" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Lsr_nat, Item_t (Nat_t, rest)))
//     // | Prim  "OR" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Or_nat, Item_t (Nat_t, rest)))
//     // | Prim  "AND" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (And_nat, Item_t (Nat_t, rest)))
//     // | Prim  "XOR" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Xor_nat, Item_t (Nat_t, rest)))
//     // | Prim  "NOT" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Not_int, Item_t (Int_t, rest)))
//     // | Prim  "NOT" []
//     //   Item_t (Nat_t, rest) ->
//     //     return (typed loc annot (Not_nat, Item_t (Int_t, rest)))
//     // (* comparison *)
//     // | Prim  "COMPARE" []
//     //   Item_t (Int_t, Item_t (Int_t, rest)) ->
//     //     return (typed loc annot (Compare Int_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (Nat_t, Item_t (Nat_t, rest)) ->
//     //     return (typed loc annot (Compare Nat_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (Bool_t, Item_t (Bool_t, rest)) ->
//     //     return (typed loc annot (Compare Bool_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (String_t, Item_t (String_t, rest)) ->
//     //     return (typed loc annot (Compare String_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (Tez_t, Item_t (Tez_t, rest)) ->
//     //     return (typed loc annot (Compare Tez_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (Key_hash_t, Item_t (Key_hash_t, rest)) ->
//     //     return (typed loc annot (Compare Key_hash_key, Item_t (Int_t, rest)))
//     // | Prim  "COMPARE" []
//     //   Item_t (Timestamp_t, Item_t (Timestamp_t, rest)) ->
//     //     return (typed loc annot (Compare Timestamp_key, Item_t (Int_t, rest)))
//     // (* comparators *)
//     // | Prim  "EQ" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Eq, Item_t (Bool_t, rest)))
//     // | Prim  "NEQ" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Neq, Item_t (Bool_t, rest)))
//     // | Prim  "LT" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Lt, Item_t (Bool_t, rest)))
//     // | Prim  "GT" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Gt, Item_t (Bool_t, rest)))
//     // | Prim  "LE" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Le, Item_t (Bool_t, rest)))
//     // | Prim  "GE" []
//     //   Item_t (Int_t, rest) ->
//     //     return (typed loc annot (Ge, Item_t (Bool_t, rest)))
//     // (* protocol *)
//     // | Prim  "MANAGER" []
//     //   Item_t (Contract_t _, rest) ->
//     //     return (typed loc annot (Manager, Item_t (Key_hash_t, rest)))
//     // | Prim  "TRANSFER_TOKENS" []
//     //   Item_t (p, Item_t
//     //             (Tez_t, Item_t
//     //                (Contract_t (cp, cr), Item_t
//     //                   (storage, Empty_t)))) ->
//     //     check_item_ty p cp loc "TRANSFER_TOKENS" 1 4 >>=? fun (Eq _) ->
//     //     begin match storage_type with
//     //       | Some storage_type ->
//     //           check_item_ty storage storage_type loc "TRANSFER_TOKENS" 3 4 >>=? fun (Eq _) ->
//     //           return (typed loc annot (Transfer_tokens storage,
//     //                              Item_t (cr, Item_t (storage, Empty_t))))
//     //       | None ->
//     //           fail (Transfer_in_lambda loc)
//     //     end
//     // | Prim  "CREATE_ACCOUNT" []
//     //   Item_t
//     //     (Key_hash_t, Item_t
//     //        (Option_t Key_hash_t, Item_t
//     //           (Bool_t, Item_t
//     //              (Tez_t, rest)))) ->
//     //     return (typed loc annot (Create_account,
//     //                        Item_t (Contract_t (Unit_t, Unit_t), rest)))
//     // | Prim  "DEFAULT_ACCOUNT" []
//     //   Item_t (Key_hash_t, rest) ->
//     //     return
//     //       (typed loc annot (Default_account, Item_t (Contract_t (Unit_t, Unit_t), rest)))
//     // | Prim  "CREATE_CONTRACT" []
//     //   Item_t
//     //     (Key_hash_t, Item_t
//     //        (Option_t Key_hash_t, Item_t
//     //           (Bool_t, Item_t
//     //              (Bool_t, Item_t
//     //                 (Tez_t, Item_t
//     //                    (Lambda_t (Pair_t (p, gp),
//     //                               Pair_t (r, gr)), Item_t
//     //                       (ginit, rest))))))) ->
//     //     check_item_ty gp gr loc "CREATE_CONTRACT" 5 7 >>=? fun (Eq _) ->
//     //     check_item_ty ginit gp loc "CREATE_CONTRACT" 6 7 >>=? fun (Eq _) ->
//     //     return (typed loc annot (Create_contract (gp, p, r),
//     //                        Item_t (Contract_t (p, r), rest)))
//     // | Prim  "NOW" []
//     //   stack ->
//     //     return (typed loc annot (Now, Item_t (Timestamp_t, stack)))
//     // | Prim  "AMOUNT" []
//     //   stack ->
//     //     return (typed loc annot (Amount, Item_t (Tez_t, stack)))
//     // | Prim  "BALANCE" []
//     //   stack ->
//     //     return (typed loc annot (Balance, Item_t (Tez_t, stack)))
//     // | Prim  "HASH_KEY" []
//     //   Item_t (Key_t, rest) ->
//     //     return (typed loc annot (Hash_key, Item_t (Key_hash_t, rest)))
//     // | Prim  "CHECK_SIGNATURE" []
//     //   Item_t (Key_t, Item_t (Pair_t (Signature_t, String_t), rest)) ->
//     //     return (typed loc annot (Check_signature, Item_t (Bool_t, rest)))
//     // | Prim  "H" []
//     //   Item_t (t, rest) ->
//     //     return (typed loc annot (H t, Item_t (String_t, rest)))
//     // | Prim  "STEPS_TO_QUOTA" []
//     //   stack ->
//     //     return (typed loc annot (Steps_to_quota, Item_t (Nat_t, stack)))
//     // | Prim  "SOURCE" [ ta; tb ]
//     //   stack ->
//     //     (Lwt.return (parse_ty ta)) >>=? fun (Ex_ty ta) ->
//     //     (Lwt.return (parse_ty tb)) >>=? fun (Ex_ty tb) ->
//     //     return (typed loc annot (Source (ta, tb), Item_t (Contract_t (ta, tb), stack)))
//     // (* Primitive parsing errors *)
//     // | Prim  ("DROP" | "DUP" | "SWAP" | "SOME" | "UNIT"
//     //              | "PAIR" | "CAR" | "CDR" | "CONS"
//     //              | "MEM" | "UPDATE" | "MAP" | "REDUCE"
//     //              | "GET" | "EXEC" | "FAIL" | "SIZE"
//     //              | "CONCAT" | "ADD" | "SUB"
//     //              | "MUL" | "EDIV" | "OR" | "AND" | "XOR"
//     //              | "NOT"
//     //              | "ABS" | "NEG" | "LSL" | "LSR"
//     //              | "COMPARE" | "EQ" | "NEQ"
//     //              | "LT" | "GT" | "LE" | "GE"
//     //              | "MANAGER" | "TRANSFER_TOKENS" | "CREATE_ACCOUNT"
//     //              | "CREATE_CONTRACT" | "NOW"
//     //              | "DEFAULT_ACCOUNT" | "AMOUNT" | "BALANCE"
//     //              | "CHECK_SIGNATURE" | "HASH_KEY"
//     //              | "H" | "STEPS_TO_QUOTA"
//     //              as name), (_ :: _ as l), _), _ ->
//     //     fail (Invalid_arity (loc, name, 0, List.length l))
//     // | Prim  ("NONE" | "LEFT" | "RIGHT" | "NIL"
//     //              | "EMPTY_SET" | "DIP" | "LOOP"
//     //              as name), ([]
//     //                        | _ :: _ :: _ as l), _), _ ->
//     //     fail (Invalid_arity (loc, name, 1, List.length l))
//     // | Prim  ("PUSH" | "IF_NONE" | "IF_LEFT" | "IF_CONS"
//     //              | "EMPTY_MAP" | "IF" | "SOURCE"
//     //              as name), ([] | [ _ ]
//     //                        | _ :: _ :: _ :: _ as l), _), _ ->
//     //     fail (Invalid_arity (loc, name, 2, List.length l))
//     // | Prim  "LAMBDA" ([] | [ _ ] | [ _ ; _ ]
//     //                        | _ :: _ :: _ :: _ :: _ as l), _), _ ->
//     //     fail (Invalid_arity (loc, "LAMBDA" 3, List.length l))
//     // (* Stack errors *)
//     // | Prim  ("ADD" | "SUB" | "MUL" | "EDIV"
//     //              | "AND" | "OR" | "XOR" | "LSL" | "LSR"
//     //              | "CONCAT" | "COMPARE" as name), [] _),
//     //   Item_t (ta, Item_t (tb, _)) ->
//     //     fail (Undefined_binop (loc, name, ta, tb))
//     // | Prim  ("NEG" | "ABS" | "NOT"
//     //              | "EQ" | "NEQ" | "LT" | "GT" | "LE" | "GE" as name),
//     //         [] _),
//     //   Item_t (t, _) ->
//     //     fail (Undefined_unop (loc, name, t))
//     // | Prim  ("REDUCE" | "UPDATE" as name), [] _),
//     //   stack ->
//     //     fail (Bad_stack (loc, name, 3, stack))
//     // | Prim  "CREATE_CONTRACT" [] _),
//     //   stack ->
//     //     fail (Bad_stack (loc, "CREATE_CONTRACT" 7, stack))
//     // | Prim  "CREATE_ACCOUNT" [] _),
//     //   stack ->
//     //     fail (Bad_stack (loc, "CREATE_ACCOUNT" 4, stack))
//     // | Prim  "TRANSFER_TOKENS" [] _),
//     //   stack ->
//     //     fail (Bad_stack (loc, "TRANSFER_TOKENS" 3, stack))
//     // | Prim  ("DROP" | "DUP" | "CAR" | "CDR" | "SOME" | "H" | "DIP"
//     //              | "IF_NONE" | "LEFT" | "RIGHT" | "IF_LEFT" | "IF"
//     //              | "LOOP" | "IF_CONS" | "MANAGER" | "DEFAULT_ACCOUNT"
//     //              | "NEG" | "ABS" | "INT" | "NOT"
//     //              | "EQ" | "NEQ" | "LT" | "GT" | "LE" | "GE" as name), _, _),
//     //   stack ->
//     //     fail (Bad_stack (loc, name, 1, stack))
//     // | Prim  ("SWAP" | "PAIR" | "CONS"
//     //              | "MAP" | "GET" | "MEM" | "EXEC"
//     //              | "CHECK_SIGNATURE" | "ADD" | "SUB" | "MUL"
//     //              | "EDIV" | "AND" | "OR" | "XOR"
//     //              | "LSL" | "LSR" | "CONCAT" as name), _, _),
//     //   stack ->
//     //     fail (Bad_stack (loc, name, 2, stack))
//     // (* Generic parsing errors *)
    | expr, sty -> None
