module Tezos.HoareWithContext

open Tezos.Primitives
open Tezos.Definitions
// open Tezos.AbstractInterpreter
open Tezos.Interpreter

// open FStar.Mul

open Tezos.ScriptRepr
module U = Tezos.UntypedDefinitions
open U
open Tezos.TezRepr
open Tezos.Storage
open Tezos.Error
open FStar.Tactics

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

noeq type state =
  {origination: origination_nonce;
   // qta: quota;
   orig:contract;
   source: contract;
   amount:tez;
   ctxt: context;
   stack: stack;
   }

type assertion = state -> Type0

let (===>) (p:assertion) (q:assertion) = forall st. p st ==> q st

(** syntactic sugar for a common operation: applying a predicate
    to a stack augmented with one element *)
val lift_stack: tagged_data -> state -> state
let lift_stack v st = {st with stack=Item v st.stack}

val lift_assert: tagged_data -> assertion -> assertion
let lift_assert v q = fun (st : state) -> q (lift_stack v st)

/// ???? does not typecheck for some weird reason. also, it prints a 3-tuple
/// instead of a 4-tuple as both the type and the expected type, which is wrong
// (** a function to make it less of a pain to call step on a whole state *)
// val wrap_step : uinstr -> state -> quota -> tzresult (stack * quota * context * origination_nonce)

let wrap_step c st f =
step st.origination f st.orig st.source st.amount st.ctxt c st.stack


val evaluate: uinstr -> state -> nat -> option state
let evaluate ui st f =
  match wrap_step ui st f with
  | Ok (sta',qta',ctxt',orig_nonce') -> Some ({st with stack=sta';ctxt=ctxt';origination=orig_nonce'})
  | Error e -> None

let spec (ui:uinstr) (p:assertion) (q:assertion) (st:state) (f:nat) =
  p st ==>
  (match evaluate ui st f with
   | Some st' -> q st'
   | _ -> True)

(** Hoare logic triples
 *
 * The pattern in the quantifier helps proving [loop_Triple] below
 * and seems generally useful to have.
 * Should we have other patterns? e.g. [spec]
 *)
let triple ui p q =
forall st f.{:pattern (evaluate ui st f)} spec ui p q st f

val implies_refl: p:assertion -> Lemma (p ===> p) [SMTPat (p ===> p)]
let implies_refl p = ()

/// Hoare logic rules

(** Spec of Transfer_tokens when the callee returns unit *)
val triple_Transfer_tokens_unit_return : #t:ty -> p:assertion -> q:assertion ->
  st:state -> f:nat -> Lemma
  (requires
  (match st.stack with
   | Item _ (Item (DTez amount)
     (Item (DContract (TC tp Unit_t dest)) (Item sto Empty))) -> begin
     let ctxt = st.ctxt in
     let src = st.source in
     match get_contract_balance ctxt src, get_contract_balance ctxt dest with
       | Ok x, Ok (vy : tez) ->
	 (fun st1 -> match get_contract_balance st1.ctxt dest with
		  | Error _ -> False
		  | Ok vy' -> vy' = vy + amount) ===> q
       | _,_ ->	False
     end
   | _ -> False))
  (ensures (spec (Transfer_tokens t) p q st f))

// For now the proof is trivial because the Transfer_tokens opcode is not implemented in the interpreter
let triple_Transfer_tokens_unit_return #t p q st f = ()

(**
 *
 * For convenience, most rules subsume weakening of the pre-condition.
 * Should we also include strengthening of the post-condition?
 *
 *)

val triple_weaken: q:assertion -> c:uinstr -> p:assertion -> r:assertion -> Lemma
  (requires (triple c q r /\ (p ===> q)))
  (ensures  (triple c p r))
let triple_weaken q c p r = ()


val triple_strengthen: r:assertion -> c:uinstr -> p:assertion -> q:assertion -> Lemma
  (requires (triple c p q /\ (q ===> r)))
  (ensures  (triple c p r))
let triple_strengthen r c p q = ()


val triple_Nop: p:assertion -> q:assertion -> Lemma
  (requires (p ===> q))
  (ensures  (triple Nop p q))
let triple_Nop p q = ()

val triple_Drop: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
      match st.stack with
      | Item _ sta' -> q ({st with stack=sta'})
      | _ -> True)))
  (ensures  (triple Drop p q))
  let triple_Drop p q = ()

val triple_Dup: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
      match st.stack with
      | Item v sta' -> q ({st with stack=(Item v (Item v sta'))})
      | _ -> True)))
  (ensures  (triple Dup p q))
let triple_Dup p q = ()

val triple_Swap: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
     match st.stack with
     | Item v (Item v' st') -> q ({st with stack=Item v' (Item v st')})
     | _ -> True)))
  (ensures (triple Swap p q))
let triple_Swap p q = ()


val triple_Eq: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
      match st.stack with
      | Item (DInt v) st' -> q ({st with stack=Item (DBool (v = 0)) st'})
      | _ -> True)))
  (ensures (triple U.Eq p q))
let triple_Eq p q = ()


val triple_Neq: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
      match st.stack with
      | Item (DInt v) st' -> q ({st with stack=(Item (DBool (v <> 0)) st')})
      | _ -> True)))
  (ensures (triple Neq p q))
let triple_Neq p q = ()


val triple_Const_int: i:int -> p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st -> q ({st with stack=Item (DInt i) st.stack}))))
  (ensures (triple (Const_int i) p q))
let triple_Const_int i p q = ()


val triple_Const_bool: b:bool -> p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st -> q ({st with stack=Item (DBool b) st.stack}))))
  (ensures (triple (Const_bool b) p q))
let triple_Const_bool b p q = ()

val triple_Const_unit: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st -> q ({st with stack=Item (DUnit) st.stack}))))
  (ensures (triple (Const_unit) p q))
let triple_Const_unit p q = ()

val triple_Sub_int: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
    match st.stack with
    | Item (DInt a) (Item (DInt b) rest) -> q ({st with stack=Item (DInt (a - b)) rest})
    | _ -> True)))
  (ensures (triple Sub_int p q))
let triple_Sub_int p q = ()


val triple_Mul_intint: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ->
    match st.stack with
    | Item (DInt a) (Item (DInt b) rest) -> q ({st with stack =Item (DInt (FStar.Mul.(a * b))) rest})
    | _ -> True)))
  (ensures (triple Mul_intint p q))
let triple_Mul_intint p q = ()

private val triple_If_aux:
  ct:uinstr -> cf:uinstr -> p:assertion -> q:assertion -> st:state ->
  f:nat -> Lemma
  (requires
    (triple ct (fun st -> p ({st with stack =(Item (DBool true) st.stack)})) q) /\
    (triple cf (fun st -> p ({st with stack=Item (DBool false) st.stack})) q))
  (ensures (spec (If ct cf) p q st f))
let triple_If_aux ct cf p q st f =
    match f with
    | 0 -> ()
    | _ ->
      begin
      match st.stack with
      | Item (DBool true) rest ->
        assert (spec ct (fun st -> p ({st with stack =Item (DBool true) st.stack})) q ({st with stack=rest}) f)
      | Item (DBool false) rest ->
        assert (spec cf (fun st -> p ({st with stack=Item (DBool false) st.stack})) q ({st with stack=rest}) f)
      | _ -> ()
      end

(**
 *
 *  {fun st -> p [true;st]} ct {q}    {fun st -> p [false;st]} cf {q}
 * ------------------------------------------------------------------- [IF]
 *                    {p} IF ct ct {q}
 *)
val triple_If: ct:uinstr -> cf:uinstr -> p:assertion -> q:assertion -> Lemma
  (requires
    (triple ct (fun st -> p ({st with stack=Item (DBool true) st.stack})) q) /\
    (triple cf (fun st -> p ({st with stack=Item (DBool false) st.stack})) q))
  (ensures (triple (If ct cf) p q))
let triple_If ct cf p q =
  assert_by_tactic (triple (If ct cf) p q)
    (norm [delta_only ["Tezos.HoareWithContext.triple"]];;
     st <-- forall_intro;
     f <-- forall_intro;
     apply_lemma (quote (triple_If_aux ct cf p q));;
     smt
  )


private val triple_Dip_aux: body:uinstr -> p:assertion -> q:assertion
  -> v:tagged_data -> st:state -> f:nat -> Lemma
  (requires (triple body (lift_assert v p) (lift_assert v q)))
  (ensures  (spec (Dip body) p q ({st with stack=Item v st.stack}) f))
  [SMTPatT (spec (Dip body) p q ({st with stack=Item v st.stack}) f)]
let triple_Dip_aux body p q v st f =
  match f with
  | 0 -> ()
  | _ -> assert (spec body (lift_assert v p) (lift_assert v q) st f)

#set-options "--z3rlimit 100 --initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"


(**
 *
 *  forall v. {fun st -> p [v;st]} c1 {fun st' -> q [v;st']}
 * ---------------------------------------------------------- [DIP]
 *                    {p} DIP body {q}
 *)
/// The problem here is probably related to the [SMTPatT] above
val triple_Dip: body:uinstr -> p:assertion -> q:assertion -> Lemma
  (requires (forall v. triple body (lift_assert v p) (lift_assert v q)))
  (ensures  (triple (Dip body) p q))
let triple_Dip body p q = admit() // assert_by_tactic (triple (Dip body) p q) (norm [delta_only ["Tezos.HoareWithContext.triple"]];;
// st <-- forall_intro;
// f <-- forall_intro;
// apply_lemma (quote (triple_Dip_aux body p q));;

// fail "coucou")

/// Not sure what's wrong here. Could be the intermediate state
private val triple_Seq_aux: c1:uinstr -> c2:uinstr -> p:assertion -> q:assertion
  -> r:assertion -> st:state -> f:nat -> Lemma
  (requires (triple c1 p q /\ triple c2 q r))
  (ensures  (spec (Seq c1 c2) p r st f))
let triple_Seq_aux c1 c2 p q r st f =
  match f with
  | 0 -> ()
  | _ ->
    assert (spec c1 p q st f);
    match wrap_step c1 st f with
    | Ok (sta',f',ctxt',orig_nonce') ->
	 let st' = ({st with stack=sta';ctxt=ctxt';origination=orig_nonce'}) in
	 assert (spec c2 q r st' f');
	 assert_by_tactic (spec (Seq c1 c2) p r st f)
	 (// norm [delta_only["Tezos.HoareWithContext.spec";
          //                  "Tezos.HoareWithContext.evaluate"]];;
	 admit())
    | _ -> ()


// private val triple_Seq_aux: c1:uinstr -> c2:uinstr -> p:assertion -> q:assertion
//   -> r:assertion -> st:stack -> f:nat -> ctxt:context -> c:contract -> Lemma
//   (requires (triple c1 p q /\ triple c2 q r))
//   (ensures  (spec (Seq c1 c2) p r st f ctxt c))
// let triple_Seq_aux c1 c2 p q r st f ctxt c =
//   match f with
//   | 0 -> ()
//   | _ ->
//     assert (spec c1 p q st f ctxt c);
//     match ueval f c1 st ctxt c with
//     | Partial f' ctxt' st' -> assert (spec c2 q r st' f' ctxt' c)
//     | _ -> ()

(**
 *
 *  {p} c1 {q}   {q} c2 {r}
 * ------------------------- [SEQ]
 *      {p} c1; c2 {r}
 *)
val triple_Seq: c1:uinstr -> c2:uinstr -> p:assertion -> q:assertion -> r:assertion -> Lemma
  (requires (triple c1 p q /\ triple c2 q r))
  (ensures  (triple (Seq c1 c2) p r))
let triple_Seq c1 c2 p q r =
  assert_by_tactic (triple (Seq c1 c2) p r)
    (norm [delta_only ["Tezos.HoareWithContext.triple"]];;
     st <-- forall_intro; rename_to st "st";;
     f <-- forall_intro;  rename_to f "f";;
     apply_lemma (quote (triple_Seq_aux c1 c2 p q r));;
     smt)


private val triple_Loop_aux: body:uinstr -> p:assertion -> q:assertion -> inv:assertion
  -> st:state -> f:nat -> Lemma
  (requires
    (p ===> inv) /\
    (triple body (fun st -> inv ({st with stack=Item (DBool true) st.stack})) inv) /\
    (forall st. inv ({st with stack=Item (DBool false) st.stack}) ==> q st))
  (ensures spec (Loop body) p q st f)
  (decreases f)
let rec triple_Loop_aux body p q inv st f =
  match f with
  | 0 -> ()
  | _ ->
    begin
    match st.stack with
    | Item (DBool true) sta' ->
      begin
      match wrap_step body ({st with stack=sta'}) f with
      | Ok (st1,f1,ctxt',origination') ->
        if f1 > 0 then
	  let st' = {st with stack=st1;ctxt=ctxt';origination=origination'} in
          triple_Loop_aux body inv q inv st' (f1 - 1);
	  assert_by_tactic (spec (Loop body) p q st f) (admit())
//          end
        // end
      | _ -> ()
      end
    | _ -> ()
    end


// private val triple_Loop_aux: body:uinstr -> p:assertion -> q:assertion -> inv:assertion
//   -> st:stack -> f:nat -> Lemma
//   (requires
//     (p ===> inv) /\
//     (triple body (fun st -> inv (Item (DBool true) st)) inv) /\
//     (forall rest. inv (Item (DBool false) rest) ==> q rest))
//   (ensures spec (Loop body) p q st f)
//   (decreases f)
// let rec triple_Loop_aux body p q inv st f =
//   match f with
//   | 0 -> ()
//   | _ ->
//     begin
//     match st with
//     | Item (DBool true) st' ->
//       begin
//       match ueval f body st' with
//       | Partial f1 st1 ->
//         begin
//         if f1 > 0 then
// //          begin
// //          assert (forall st f.{:pattern ueval f body st}
// //            inv (Item (DBool true) st) ==>
// //            spec body (fun st -> inv (Item (DBool true) st)) inv st f);
// //          assert (ueval f (Loop body) st == ueval (f1 - 1) (Loop body) st1);
// //          assert (inv st ==> inv st1);
//           triple_Loop_aux body inv q inv st1 (f1 - 1)
// //          end
//         end
//       | _ -> ()
//       end
//     | _ -> ()
//     end

(**
 *
 *    p ===> inv
 *    {fun st -> inv [true;st]} body {inv}
 *    forall st. inv [false;st] ==> q st
 *  --------------------------------------- [LOOP]
 *              {p} Loop body {q}
 *
 * REMARK:
 * The invariant operates over the stack *including* the boolean condition.
 *
 *)
// val triple_Loop: body:uinstr -> p:assertion -> q:assertion -> inv:assertion -> Lemma
//   (requires
//     (p ===> inv) /\
//     (triple body (fun st -> inv (Item (DBool true) st)) inv) /\
//     (forall rest. inv (Item (DBool false) rest) ==> q rest))
//   (ensures triple (Loop body) p q)
// let triple_Loop body p q inv =
//   (* Avoid pattern in auxiliary lemma at the cost of using tactics here *)
//   assert_by_tactic (triple (Loop body) p q)
//     (norm [delta_only ["Tezos.Hoare.triple"]];;
//      forall_intros;;
//      apply_lemma (quote (triple_Loop_aux body p q inv)))


val triple_Loop: body:uinstr -> p:assertion -> q:assertion -> inv:assertion -> Lemma
  (requires
    (p ===> inv) /\
    (triple body (fun st -> inv ({st with stack=Item (DBool true) st.stack})) inv) /\
    (forall st. inv ({st with stack=Item (DBool false) st.stack}) ==> q st))
  (ensures triple (Loop body) p q)
let triple_Loop body p q inv =
  (* Avoid pattern in auxiliary lemma at the cost of using tactics here *)
  assert_by_tactic (triple (Loop body) p q)
    (norm [delta_only ["Tezos.HoareWithContext.triple"]];;
     forall_intros;;
     apply_lemma (quote (triple_Loop_aux body p q inv)))

/// The statement of triple_Exec_aux needs to change, not sure how
val triple_Exec_aux : (p:assertion) -> (q:assertion) -> st:state -> f:nat ->
Lemma
(requires
  (match st.stack with
   | Item arg (Item (DLambda (Lam ta tb ui e)) rest) ->
     triple ui
       (fun st ->
	  st.stack == Item arg Empty /\
	  p ({st with
	      stack=Item arg (Item (DLambda (Lam ta tb ui e)) rest)}))
       (fun st -> match st.stack with
	       | Item y Empty -> q ({st with stack=Item y rest})
	       | _ -> False)
   | _ -> True))
(ensures spec Exec p q st f)

let triple_Exec_aux p q st f = admit()


// val triple_Exec_aux : (p : assertion) -> (q : assertion) -> st:stack -> f : nat ->
// Lemma
// (requires (match st with
// 	    | Item arg (Item (DLambda ta tb e ui) rest) ->
// 	      // let u x = p (Item x (Item (DLambda ta tb e ui) rest)) in
// 	      let v y = q (Item y (rest)) in
// 	      // let u' stx = match stx with
// 	      //		     | Item arg' UEmpty -> u arg'
// 	      //		     | _ -> True in
// 	      let v' sty = match sty with
// 			     | Item res UEmpty -> v res
// 			     | _ -> False in
// 	      triple ui (fun st -> st == Item arg UEmpty /\ p (Item arg (Item (DLambda ta tb e ui) rest))) v'
// 	    | _ -> True))
// (ensures spec Exec p q st f)

// let triple_Exec_aux p q st f = ()


// val step_fuel_monotonic: f:nat -> c:uinstr -> st:state -> Lemma
//   (requires True)
//   (ensures (match wrap_step c st f,wrap_step c st (f+1)
//   with
//    | Ok(sta1,f1,ctxt1,on1), Ok(sta2,f2,ctxt2,on2) -> f2 == f1 + 1 /\ sta1 == sta2
//    | Ok _, _ -> False
//    | _ -> True))(decreases %[f; c])
// let rec step_fuel_monotonic f c st =
//   match c, st.stack with
//   | Loop body, Item (DBool true) rest ->
//     begin
//     step_fuel_monotonic f body st;
//     match step st.origination f st.orig st.source st.amount st.ctxt body rest with
//     | Ok(st',f',_,_) -> assert(f' <= f);
//       if f' > 0 then step_fuel_monotonic (f' - 1) (Loop body) st'
//     | _ -> ()
//     end

//   | Seq c1 c2, st ->
//     begin
//     match wrap_step c1 f st with
//     | Ok(st1,f1,_,_) ->
//       begin
//       step_fuel_monotonic f c1 st;
//       step_fuel_monotonic f1 c2 st1
//       end
//     | _ -> ()
//     end

//   | Dip c, Item v rest ->
//     step_fuel_monotonic f c rest

//   | If ct _, Item (DBool true) rest ->
//     step_fuel_monotonic f ct rest

//   | If _ cf, Item (DBool false) rest ->
//     step_fuel_monotonic f cf rest

//   | If_none ct _, Item (DOption None) rest ->
//     step_fuel_monotonic f ct rest

//   | If_none _ cf, Item (DOption (Some v)) rest ->
//     step_fuel_monotonic f cf (Item v rest)

//   | Exec, Item arg (Item (DLambda ta tb e ui') rest) ->
//     if f > 0 then step_fuel_monotonic (f - 1) ui' (Item arg Empty)

//   | _ -> ()


// (**
//  * When [ueval] succeeds, the resulting stack is independent of the fuel
//  * also fuel consumption is independent of the amount of fuel
//  *)
// val ueval_fuel_monotonic: f:nat -> c:uinstr -> st:stack -> Lemma
//   (match ueval f c st, ueval (f + 1) c st with
//    | Partial f1 st1, Partial f2 st2 -> f2 == f1 + 1 /\ st1 == st2
//    | Partial _ _, _ -> False
//    | _ -> True)
// let rec ueval_fuel_monotonic f c st =
//   match c, st with
//   | Loop body, Item (DBool true) st ->
//     begin
//     ueval_fuel_monotonic f body st;
//     match ueval f body st with
//     | Partial f' st' ->
//       if f' > 0 then ueval_fuel_monotonic (f' - 1) (Loop body) st'
//     | _ -> ()
//     end

//   | Seq c1 c2, st ->
//     begin
//     match ueval f c1 st with
//     | Partial f1 st1 ->
//       begin
//       ueval_fuel_monotonic f c1 st;
//       ueval_fuel_monotonic f1 c2 st1
//       end
//     | _ -> ()
//     end

//   | Dip c, Item v rest ->
//     ueval_fuel_monotonic f c rest

//   | If ct _, Item (DBool true) rest ->
//     ueval_fuel_monotonic f ct rest

//   | If _ cf, Item (DBool false) rest ->
//     ueval_fuel_monotonic f cf rest

//   | If_none ct _, Item (DOption None) rest ->
//     ueval_fuel_monotonic f ct rest

//   | If_none _ cf, Item (DOption (Some v)) rest ->
//     ueval_fuel_monotonic f cf (Item v rest)

//   | Exec, Item arg (Item (DLambda ta tb e ui') rest) ->
//     if f > 0 then ueval_fuel_monotonic (f - 1) ui' (Item arg UEmpty)

//   | _ -> ()


(**
 * Part of the proof of loop unrolling.
 *
 * For the [false] case,
 * [assert_norm (ueval f (Loop body) (Item (DBool false) st) == Partial f st);
 *  assert_norm (ueval f (If (Seq body (Loop body)) Nop) (Item (DBool false) st) ==
 *               Partial f st)]
 *)
val unroll_loop_true: body:uinstr -> f:nat -> st:stack -> Lemma
  (match ueval f (Loop body) (Item (DBool true) st),
         ueval f (Seq body (Loop body)) st
   with
   | Partial f1 st1, Partial f2 st2 -> f2 == f1 + 1 /\ st1 == st2
   | _ -> True)
let unroll_loop_true body f st =
 match f with
 | 0 -> ()
 | _ ->
   begin
   match ueval f body st with
   | Partial f1 st1 ->
     if f1 > 0 then
      (ueval_fuel_monotonic (f1 - 1) (Loop body) st1;
       assert_norm (ueval f (Loop body) (Item (DBool true) st) ==
                    ueval (f1 - 1) (Loop body) st1);
       assert_norm (ueval f (Seq body (Loop body)) st ==
                    ueval f1 (Loop body) st1))
     else ()
   | _ -> ()
   end


(** Weakest liberal precondition *)
val wp: ui:uinstr -> q:assertion -> assertion
let rec wp ui q =
  match ui with
  | Nop -> q

  | Drop -> //fun st -> Item? st ==> q (Item?.rest st)
    (fun st ->
      match st with
      | Item _ st' -> q st'
      | _ -> True)

  | Dup ->
    (fun st ->
      match st with
      | Item v st' -> q (Item v (Item v st'))
      | _ -> True)

  | Dip body ->
    (fun st ->
      match st with
      | Item v st' -> wp body (lift_assert v q) st'
      | _ -> True)

  | Swap ->
    (fun st ->
      match st with
      | Item v (Item v' st') -> q (Item v' (Item v st'))
      | _ -> True)

  | U.Eq ->
    (fun st ->
      match st with
      | Item (DInt v) st' -> q (Item (DBool (v = 0)) st')
      | _ -> True)

  | U.Neq ->
    (fun st ->
      match st with
      | Item (DInt v) st' -> q (Item (DBool (v <> 0)) st')
      | _ -> True)

  | Const_int i  -> (fun st -> q (Item (DInt i) st))

  | Const_bool b -> (fun st -> q (Item (DBool b) st))

  | Sub_int ->
    (fun st ->
      match st with
      | Item (DInt a) (Item (DInt b) rest) -> q (Item (DInt (a - b)) rest)
      | _ -> True)

  | Mul_intint ->
    (fun st ->
      match st with
      | Item (DInt a) (Item (DInt b) rest) -> q (Item (DInt (a * b)) rest)
      | _ -> True)

  | If bt bf ->
    (fun st ->
      match st with
      | Item (DBool true)  st' -> wp bt q st'
      | Item (DBool false) st' -> wp bf q st'
      | _ -> True)

  | Seq c1 c2 -> wp c1 (wp c2 q)

  | Lambda arg ret e c -> (fun st -> q (Item (DLambda arg ret e c) st))

  // | Exec -> (fun st ->
  //          match st with
  //          | Item arg (Item (DLambda ta tb e ui') rest) ->
  //              wp ui' q (Item arg rest)
  //          | _ -> True)

  | _ -> fun st -> False


(** Case analysis on [stack] *)
val stack_ind: st:stack -> p:Type
  -> (squash (st == UEmpty ==> p))
  -> (squash (forall v rest. st == Item v rest ==> p))
  -> Lemma p
let stack_ind st p h1 h2 = ()

let cases_stack (st:term) : tactic unit =
  si <-- quote_lid ["Tezos";"Hoare";"stack_ind"];
  seq (apply_lemma (return (mk_e_app si [st])))
      (trytac (eq <-- implies_intro; rewrite eq;; clear_top);;
       trytac (v <-- forall_intro; rest <-- forall_intro;
               eq <-- implies_intro; rewrite eq;; clear_top);;
       idtac)

private val wp_Dip_body: c:uinstr -> q:assertion -> v:tagged_data -> st:stack -> Lemma
  (requires (wp (Dip c) q (Item v st)))
  (ensures  (wp c (fun st -> q (Item v st)) st))
let wp_Dip_body c q v st = ()

(** Soundness of [wp]; subsumes weakening *)
val wp_correct: ui:uinstr -> p:assertion -> q:assertion -> Lemma
  (requires (p ===> wp ui q))
  (ensures  (triple ui p q))
  [SMTPat (triple ui p q)]
let rec wp_correct ui p q =
  match ui with
  | Nop -> triple_Nop (wp Nop q) q

  | Drop -> triple_Drop (wp Drop q) q

  | Dup -> triple_Dup (wp Dup q) q

  | Dip body ->
    assert_by_tactic (triple (Dip body) p q)
      (norm [delta_only ["Tezos.Hoare.triple"]];;
       st <-- forall_intro; f  <-- forall_intro;
       cases_stack (pack (Tv_Var st));;
       (**) smt;;
       (**) mapply (quote triple_Dip_aux);;
            mapply (quote wp_correct);;
            norm [delta_only ["Tezos.Hoare.op_Equals_Equals_Equals_Greater"]];;
            st' <-- forall_intro; h <-- implies_intro;
            mapply (quote (wp_Dip_body body q)))

  | Swap -> triple_Swap (wp Swap q) q

  | U.Eq -> triple_Eq (wp Eq q) q

  | U.Neq -> triple_Neq (wp Neq q) q

  | Const_int i -> triple_Const_int i (wp (Const_int i) q) q

  | Const_bool b -> triple_Const_bool b (wp (Const_bool b) q) q

  | Sub_int -> triple_Sub_int (wp Sub_int q) q

  | Mul_intint -> triple_Mul_intint (wp Mul_intint q) q

  | If ct cf ->
    assert_by_tactic (triple (If ct cf) p q)
      (mapply (quote triple_If);;
       seq split (mapply (quote wp_correct)))

  | Seq c1 c2 ->
    assert_by_tactic (triple (Seq c1 c2) p q)
      (mapply (quote (triple_Seq c1 c2 p (wp c2 q)));;
       seq split (mapply (quote wp_correct)))

  | _ -> ()

let by_wp: tactic unit = mapply (quote wp_correct);; norm [delta]


/// Examples

let toy_lambda = (Dup >> Mul_intint)
let toy_stack = (Item (DInt 3) (Item (DLambda Int_t Int_t (String "") toy_lambda)UEmpty))

val toy_p : assertion
let toy_p = (fun st -> st == Item (DInt 3) (Item (DLambda Int_t Int_t (String "") (Seq Dup Mul_intint)) UEmpty))
val toy_q : assertion
let toy_q = (fun st -> st == Item (DInt 9) UEmpty)

val toy_correct : st : stack -> f : nat -> Lemma (spec Exec toy_p toy_q st f)

let toy_correct st f =
 match st with
   | Item arg (Item (DLambda ta tb e (Seq Dup Mul_intint)) rest) ->
   assert_by_tactic
     (spec Exec toy_p toy_q (Item arg (Item (DLambda ta tb e (Seq Dup Mul_intint)) rest)) f)
     (apply_lemma (quote (triple_Exec_aux toy_p toy_q));;
     by_wp)
   | _ -> ()


/// Simple no-op program

let prog : uinstr = Dup >> Drop

val prog_triple: st0:stack ->
  Lemma (triple prog (fun st -> st == st0) (fun st -> st == st0))
let prog_triple st0 =
  assert_by_tactic (triple prog (fun st -> st == st0) (fun st -> st == st0)) by_wp


/// Factorial

(** Inner loop *)
let loop: uinstr =
  (* [ (n <> 0)? ; n; acc ] *)
  (
    (* [ n ; acc ] *)
    Dup >>
    (* [ n ; n ; acc ] *)
    Dip ( Mul_intint ) >>
    (* [ n ; n * acc ] *)
    Const_int 1 >>
    (* [ 1 ; n ; n * acc ] *)
    Swap >>
    (* [ n ; 1 ; n * acc ] *)
    Sub_int >>
    (* [ n-1 ; n * acc ] *)
    Dup >>
    (* [ n-1 ; n-1 ; n * acc ] *)
    U.Neq
    (* [ (n-1 <> 0)? ; n-1 ; n * acc ] *)
  )

(** Factorial program *)
let factorial: uinstr =
  (* [ n ] -- input parameter, n >= 0 *)
  Dup >>
  (* [ n ; n ] *)
  U.Eq >>
  (* [ (n = 0)? ; n ] *)
  If ( Drop >>
       (* [] *)
       Const_int 1
       (* [ 1 ] *)
     ) (* return 0! = 1 *)
     ( Const_int 1 >>    (* accumulator's initial value *)
       (* [ 1; n ] *)    (* acc = 1, 0 < n *)
       Swap >>
       (* [ n; 1 ] *)
       Dup >>
       (* [ n; n; 1 ] *)
       Neq >>
       (* [ (n <> 0)?; n; 1 ] *)
       Loop loop >>
       (* [ 0; fact n ] *)
       Drop
       (* [ fact n ] *)
     ) (* return n! *)

(** Factorial function *)
val fact: nat -> nat
let rec fact = function
 | 0 -> 1
 | n -> n * fact (n - 1)

(**
 * The loop invariant
 *
 * 1. {inv} Loop loop {inv}
 * 2. inv /\ top_false ==> acc = fact m
 *)
val inv: nat -> assertion
let inv m = function
  | Item (DBool b) (Item (DInt n) (Item (DInt acc) _)) ->
    b == (n <> 0) /\ 0 <= n /\ fact n * acc == fact m
  | _ -> False

val post: nat -> assertion
let post m = function
  | Item (DInt n) (Item (DInt acc) _) ->
    n == 0 /\ 1 * acc == fact m // Yes, the `1 *` is needed
  | _ -> False

(** When entered, [loop] restablishes the invariant:
 *  {fun st -> inv m [true;st]} loop {inv},
 * put otherwise
 *  [inv [true;st] ==> wp loop inv st
 *)
private val wp_loop_inv_true_: m:nat -> st:stack -> Lemma
  (requires inv m (Item (DBool true) st))
  (ensures  wp loop (inv m) st)
let wp_loop_inv_true_ m st =
  match st with
  | Item (DInt n) (Item (DInt acc) rest) ->
    assert (0 <= n - 1 /\ fact (n - 1) * (n * acc) == fact m);
    assert_norm (wp loop (inv m) (Item (DInt n) (Item (DInt acc) rest)))
  | _ -> ()

private val wp_loop_inv_true: m:nat -> Lemma
  ((fun st -> inv m (Item (DBool true) st)) ===> wp loop (inv m))
let wp_loop_inv_true m =
  Classical.forall_intro (Classical.move_requires (wp_loop_inv_true_ m))

(** [inv [false;st] ==> post st *)
private val wp_loop_inv_false: m:nat -> Lemma
  ((fun st -> inv m (Item (DBool false) st)) ===> post m)
let wp_loop_inv_false m = ()

val loop_triple: m:nat -> Lemma (triple (Loop loop) (inv m) (post m))
let loop_triple m =
  assert_by_tactic (triple (Loop loop) (inv m) (post m))
    (mapply (quote triple_Loop);;
     exact (quote (inv m));;
     split;;
       split;;
       mapply (quote implies_refl);;
       mapply (quote wp_correct);;
         mapply (quote wp_loop_inv_true);;
         mapply (quote wp_loop_inv_false))

val p: nat -> assertion
let p m = function
  | Item (DInt n) _ -> n == m
  | _ -> True

val q: nat -> assertion
let q m = function
  | Item (DInt acc) _ -> acc == fact m
  | _ -> False

val r: nat -> assertion
let r m = function
  | Item (DBool b) (Item (DInt n) _) -> b == (m = 0) /\ n == m
  | _ -> False

(**
  * REMARK:
  * The last SMT goal (post m [n;acc;_] ==> q m [acc;st]) requires one extra inversion.
  * The corresponding hint isn't replayable for some reason.
  * This is the only non-replayable hint in the whole file.
  *)
#set-options "--initial_ifuel 2 --max_ifuel 2"

val factorial_spec: m:nat -> Lemma (triple factorial (p m) (q m))
let factorial_spec m =
  assert_by_tactic (triple factorial (p m) (q m))
    (mapply (quote triple_Seq);;
     exact (quote (r m));;
     split;;
     (**) by_wp;; smt;;
     (**) mapply (quote triple_If);;
          split;;
          (**) by_wp;; smt;;
          (**) mapply (quote triple_Seq);;
               exact (quote (post m));;
               split;;
               (**) mapply (quote triple_Seq);;
                    exact (quote (inv m));;
                    split;;
                    (**) by_wp;; smt;;
                    (**) mapply (quote loop_triple);;
               (**) by_wp)
