module Tezos.Hoare

open Tezos.Primitives
open Tezos.Definitions
open Tezos.Storage
open Tezos.AbstractInterpreter

open FStar.Mul
open FStar.Tactics

module U = Tezos.UntypedDefinitions
open U

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type assertion = stack -> context -> contract -> Type0

let (===>) (p:assertion) (q:assertion) =
  forall st ctxt src. p st ctxt src ==> q st ctxt src

(** Syntactic sugar for a common operation: applying a predicate
    to a stack augmented with one element *)
val lift_assert: tagged_data -> assertion -> assertion
let lift_assert v q = fun st ctxt src -> q (UItem v st) ctxt src

// REMARK: Can't write a val because of #638
let spec (c:uinstr) (pre:assertion) (post:assertion)
         (st:stack) (ctxt:context) (src:contract) (f:nat) : Type0 =
  pre st ctxt src ==>
  (match ueval f c st ctxt src with
   | Partial _ ctxt' st' -> post st' ctxt' src
   | _ -> True)


(** Hoare logic triples
 *
 * The pattern in the quantifier helps proving [loop_Triple] below
 * and seems generally useful to have.
 * Should we have other patterns? e.g. [spec]
 *)
let triple c pre post =
  forall st ctxt src f.{:pattern (ueval f c st ctxt src)}
    spec c pre post st ctxt src f

val implies_refl: p:assertion -> Lemma (p ===> p) [SMTPat (p ===> p)]
let implies_refl p = ()

/// Hoare logic rules

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
  (requires (p ===> (fun st ctxt src ->
      match st with
      | UItem _ st' -> q st' ctxt src
      | _ -> True)))
  (ensures  (triple Drop p q))
let triple_Drop p q = ()


val triple_Dup: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
      match st with
      | UItem v st' -> q (UItem v (UItem v st')) ctxt src
      | _ -> True)))
  (ensures  (triple Dup p q))
let triple_Dup p q = ()


val triple_Swap: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
     match st with
     | UItem v (UItem v' st') -> q (UItem v' (UItem v st')) ctxt src
     | _ -> True)))
  (ensures (triple Swap p q))
let triple_Swap p q = ()


val triple_Eq: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
      match st with
      | UItem (DInt v) st' -> q (UItem (DBool (v = 0)) st') ctxt src
      | _ -> True)))
  (ensures (triple U.Eq p q))
let triple_Eq p q = ()


val triple_Neq: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
      match st with
      | UItem (DInt v) st' -> q (UItem (DBool (v <> 0)) st') ctxt src
      | _ -> True)))
  (ensures (triple Neq p q))
let triple_Neq p q = ()


val triple_Const_int: i:int -> p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st -> q (UItem (DInt i) st))))
  (ensures (triple (Const_int i) p q))
let triple_Const_int i p q = ()


val triple_Const_bool: b:bool -> p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st -> q (UItem (DBool b) st))))
  (ensures (triple (Const_bool b) p q))
let triple_Const_bool b p q = ()


val triple_Sub_int: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
    match st with
    | UItem (DInt a) (UItem (DInt b) rest) -> q (UItem (DInt (a - b)) rest) ctxt src
    | _ -> True)))
  (ensures (triple Sub_int p q))
let triple_Sub_int p q = ()


val triple_Mul_intint: p:assertion -> q:assertion -> Lemma
  (requires (p ===> (fun st ctxt src ->
    match st with
    | UItem (DInt a) (UItem (DInt b) rest) -> q (UItem (DInt (a * b)) rest) ctxt src
    | _ -> True)))
  (ensures (triple Mul_intint p q))
let triple_Mul_intint p q = ()


private val triple_If_aux:
  ct:uinstr -> cf:uinstr -> p:assertion -> q:assertion ->
  st:stack -> ctxt:context -> src:contract -> f:nat -> Lemma
  (requires
    (triple ct (fun st -> p (UItem (DBool true)  st)) q) /\
    (triple cf (fun st -> p (UItem (DBool false) st)) q))
  (ensures (spec (If ct cf) p q st ctxt src f))
let triple_If_aux ct cf p q st ctxt src f =
    match f with
    | 0 -> ()
    | _ ->
      begin
      match st with
      | UItem (DBool true) rest ->
        assert (spec ct (fun st -> p (UItem (DBool true)  st)) q rest ctxt src f)
      | UItem (DBool false) rest ->
        assert (spec cf (fun st -> p (UItem (DBool false) st)) q rest ctxt src f)
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
    (triple ct (fun st -> p (UItem (DBool true)  st)) q) /\
    (triple cf (fun st -> p (UItem (DBool false) st)) q))
  (ensures (triple (If ct cf) p q))
let triple_If ct cf p q =
  assert_by_tactic (triple (If ct cf) p q)
    (norm [delta_only ["Tezos.Hoare.triple"]];;
     st <-- forall_intro;
     f <-- forall_intro;
     ctxt <-- forall_intro;
     src <-- forall_intro;
     apply_lemma (quote (triple_If_aux)))


private val triple_Dip_aux: body:uinstr -> p:assertion -> q:assertion
  -> v:tagged_data -> st:stack -> ctxt:context -> src:contract -> f:nat -> Lemma
  (requires (triple body (fun st -> p (UItem v st)) (fun st -> q (UItem v st))))
  (ensures  (spec (Dip body) p q (UItem v st) ctxt src f))
  [SMTPatT (spec (Dip body) p q (UItem v st) ctxt src f)]
let triple_Dip_aux body p q v st ctxt src f =
  match f with
  | 0 -> ()
  | _ -> assert (spec body (fun st -> p (UItem v st)) (fun st -> q (UItem v st)) st ctxt src f)

(**
 *
 *  forall v. {fun st -> p [v;st]} c1 {fun st' -> q [v;st']}
 * ---------------------------------------------------------- [DIP]
 *                    {p} DIP body {q}
 *)
val triple_Dip: body:uinstr -> p:assertion -> q:assertion -> Lemma
  (requires (forall v. triple body (fun st -> p (UItem v st)) (fun st -> q (UItem v st))))
  (ensures  (triple (Dip body) p q))
let triple_Dip body p q = ()


private val triple_Seq_aux: c1:uinstr -> c2:uinstr -> p:assertion -> q:assertion
  -> r:assertion -> st:stack -> ctxt:context -> src:contract -> f:nat -> Lemma
  (requires (triple c1 p q /\ triple c2 q r))
  (ensures  (spec (Seq c1 c2) p r st ctxt src f))
let triple_Seq_aux c1 c2 p q r st ctxt src f =
  match f with
  | 0 -> ()
  | _ ->
    assert (spec c1 p q st ctxt src f);
    match ueval f c1 st ctxt src with
    | Partial f' ctxt' st' -> assert (spec c2 q r st' ctxt src f')
    | _ -> ()


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
    (norm [delta_only ["Tezos.Hoare.triple"]];;
     st <-- forall_intro; rename_to st "st";;
     ctxt <-- forall_intro;  rename_to ctxt "ctxt";;
     src <-- forall_intro;  rename_to src "src";;
     f <-- forall_intro;  rename_to f "f";;
     apply_lemma (quote (triple_Seq_aux c1 c2 p q r));;
     smt)


private val triple_Loop_aux: body:uinstr -> p:assertion -> q:assertion -> inv:assertion
  -> st:stack -> ctxt:context -> src:contract -> f:nat -> Lemma
  (requires
    (p ===> inv) /\
    (triple body (fun st -> inv (UItem (DBool true) st)) inv) /\
    (forall rest ctxt src. inv (UItem (DBool false) rest) ctxt src ==> q rest ctxt src))
  (ensures spec (Loop body) p q st ctxt src f)
  (decreases f)
let rec triple_Loop_aux body p q inv st ctxt src f =
  match f with
  | 0 -> ()
  | _ ->
    begin
    match st with
    | UItem (DBool true) st' ->
      begin
      match ueval f body st' ctxt src with
      | Partial f1 ctxt1 st1 ->
        begin
        if f1 > 0 then
//          begin
//          assert (forall st f.{:pattern ueval f body st}
//            inv (UItem (DBool true) st) ==>
//            spec body (fun st -> inv (UItem (DBool true) st)) inv st f);
//          assert (ueval f (Loop body) st == ueval (f1 - 1) (Loop body) st1);
//          assert (inv st ==> inv st1);
          triple_Loop_aux body inv q inv st1 ctxt1 src (f1 - 1)
//          end
        end
      | _ -> ()
      end
    | _ -> ()
    end

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
val triple_Loop: body:uinstr -> p:assertion -> q:assertion -> inv:assertion -> Lemma
  (requires
    (p ===> inv) /\
    (triple body (fun st -> inv (UItem (DBool true) st)) inv) /\
    (forall rest ctxt src. inv (UItem (DBool false) rest) ctxt src ==> q rest ctxt src))
  (ensures triple (Loop body) p q)
let triple_Loop body p q inv =
  (* Avoid pattern in auxiliary lemma at the cost of using tactics here *)
  assert_by_tactic (triple (Loop body) p q)
    (norm [delta_only ["Tezos.Hoare.triple"]];;
     forall_intros;;
     apply_lemma (quote (triple_Loop_aux body p q inv)))


val triple_Exec_aux: p:assertion -> q:assertion -> st:stack -> ctxt:context -> src:contract -> f:nat ->
  Lemma
    (requires (match st with
	       | UItem arg (UItem (DLambda (Lam ta tb ui e)) rest) ->
                 p (UItem arg (UItem (DLambda (Lam ta tb ui e)) rest)) ctxt src /\
	         (let v' sty ctxt src =
                   match sty with
		   | UItem res UEmpty -> q (UItem res rest) ctxt src
		   | _ -> False in
	          triple ui (fun st ctxt src -> st == UItem arg UEmpty) v')
	       | _ -> True))
  (ensures spec Exec p q st ctxt src f)
let triple_Exec_aux p q st ctxt src f = ()


(**
 * When [ueval] succeeds, the resulting stack is independent of the fuel
 * also fuel consumption is independent of the amount of fuel
 *)
val ueval_fuel_monotonic: f:nat -> c:uinstr -> st:stack -> ctxt:context -> src:contract -> Lemma
  (match ueval f c st ctxt src, ueval (f + 1) c st ctxt src with
   | Partial f1 ctxt1 st1, Partial f2 ctxt2 st2 -> f2 == f1 + 1 /\ st1 == st2 /\ ctxt1 == ctxt2
   | Partial _ _ _, _ -> False
   | _ -> True)
let rec ueval_fuel_monotonic f c st ctxt src =
  match c, st with
  | Loop body, UItem (DBool true) st ->
    begin
    ueval_fuel_monotonic f body st ctxt src;
    match ueval f body st ctxt src with
    | Partial f' ctxt' st' ->
      if f' > 0 then ueval_fuel_monotonic (f' - 1) (Loop body) st' ctxt' src
    | _ -> ()
    end

  | Seq c1 c2, st ->
    begin
    match ueval f c1 st ctxt src with
    | Partial f1 ctxt1 st1 ->
      begin
      ueval_fuel_monotonic f c1 st ctxt src;
      ueval_fuel_monotonic f1 c2 st1 ctxt1 src
      end
    | _ -> ()
    end

  | Dip c, UItem v rest ->
    ueval_fuel_monotonic f c rest ctxt src

  | If ct _, UItem (DBool true) rest ->
    ueval_fuel_monotonic f ct rest ctxt src

  | If _ cf, UItem (DBool false) rest ->
    ueval_fuel_monotonic f cf rest ctxt src

  | If_none ct _, UItem (DOption None) rest ->
    ueval_fuel_monotonic f ct rest ctxt src

  | If_none _ cf, UItem (DOption (Some v)) rest ->
    ueval_fuel_monotonic f cf (UItem v rest) ctxt src

  | Exec, UItem arg (UItem (DLambda (Lam ta tb ui' e)) rest) ->
    if f > 0 then ueval_fuel_monotonic (f - 1) ui' (UItem arg UEmpty) ctxt src

  | _ -> ()


(**
 * Part of the proof of loop unrolling.
 *
 * For the [false] case,
 * [assert_norm (ueval f (Loop body) (UItem (DBool false) st) == Partial f st);
 *  assert_norm (ueval f (If (Seq body (Loop body)) Nop) (UItem (DBool false) st) ==
 *               Partial f st)]
 *)
val unroll_loop_true: body:uinstr -> f:nat -> st:stack -> ctxt:context -> src:contract -> Lemma
  (match ueval f (Loop body) (UItem (DBool true) st) ctxt src,
         ueval f (Seq body (Loop body)) st ctxt src
   with
   | Partial f1 ctxt1 st1, Partial f2 ctxt2 st2 -> f2 == f1 + 1 /\ st1 == st2 /\ ctxt1 == ctxt2
   | _ -> True)
let unroll_loop_true body f st ctxt src =
 match f with
 | 0 -> ()
 | _ ->
   begin
   match ueval f body st ctxt src with
   | Partial f1 ctxt1 st1 ->
     if f1 > 0 then
      (ueval_fuel_monotonic (f1 - 1) (Loop body) st1 ctxt1 src;
       assert_norm (ueval f (Loop body) (UItem (DBool true) st) ctxt src ==
                    ueval (f1 - 1) (Loop body) st1 ctxt1 src);
       assert_norm (ueval f (Seq body (Loop body)) st ctxt src ==
                    ueval f1 (Loop body) st1 ctxt1 src))
     else ()
   | _ -> ()
   end


(** Weakest liberal precondition *)
val wp: ui:uinstr -> q:assertion -> assertion
let rec wp ui q =
  match ui with
  | Nop -> q

  | Drop -> //fun st -> UItem? st ==> q (UItem?.rest st)
    (fun st ->
      match st with
      | UItem _ st' -> q st'
      | _ -> fun _ _ -> True)

  | Dup ->
    (fun st ->
      match st with
      | UItem v st' -> q (UItem v (UItem v st'))
      | _ -> fun _ _ -> True)

  | Dip body ->
    (fun st ->
      match st with
      | UItem v st' -> wp body (lift_assert v q) st'
      | _ -> fun _ _ -> True)

  | Swap ->
    (fun st ->
      match st with
      | UItem v (UItem v' st') -> q (UItem v' (UItem v st'))
      | _ -> fun _ _ -> True)

  | U.Eq ->
    (fun st ->
      match st with
      | UItem (DInt v) st' -> q (UItem (DBool (v = 0)) st')
      | _ -> fun _ _ -> True)

  | U.Neq ->
    (fun st ->
      match st with
      | UItem (DInt v) st' -> q (UItem (DBool (v <> 0)) st')
      | _ -> fun _ _ -> True)

  | Const_int i  -> (fun st -> q (UItem (DInt i) st))

  | Const_bool b -> (fun st -> q (UItem (DBool b) st))

  | Sub_int ->
    (fun st ->
      match st with
      | UItem (DInt a) (UItem (DInt b) rest) -> q (UItem (DInt (a - b)) rest)
      | _ -> fun _ _ -> True)

  | Mul_intint ->
    (fun st ->
      match st with
      | UItem (DInt a) (UItem (DInt b) rest) -> q (UItem (DInt (a * b)) rest)
      | _ -> fun _ _ -> True)

  | If bt bf ->
    (fun st ->
      match st with
      | UItem (DBool true)  st' -> wp bt q st'
      | UItem (DBool false) st' -> wp bf q st'
      | _ -> fun _ _ -> True)

  | Seq c1 c2 -> wp c1 (wp c2 q)

  | Lambda (Lam arg ret c e) -> (fun st -> q (UItem (DLambda (Lam arg ret c e)) st))

  // | Exec -> (fun st ->
  //          match st with
  //          | UItem arg (UItem (DLambda ta tb e ui') rest) ->
  //              wp ui' q (UItem arg rest)
  //          | _ -> True)

  | _ -> fun st ctxt src -> False


(** Case analysis on [stack] *)
val stack_ind: st:stack -> p:Type
  -> (squash (st == UEmpty ==> p))
  -> (squash (forall v rest. st == UItem v rest ==> p))
  -> Lemma p
let stack_ind st p h1 h2 = ()

let cases_stack (st:term) : tactic unit =
  si <-- quote_lid ["Tezos";"Hoare";"stack_ind"];
  seq (apply_lemma (return (mk_e_app si [st])))
      (trytac (eq <-- implies_intro; rewrite eq;; clear_top);;
       trytac (v <-- forall_intro; rest <-- forall_intro;
               eq <-- implies_intro; rewrite eq;; clear_top);;
       idtac)

private val wp_Dip_body: c:uinstr -> q:assertion -> v:tagged_data -> st:stack -> ctxt:context -> src:contract -> Lemma
  (requires (wp (Dip c) q (UItem v st) ctxt src))
  (ensures  (wp c (fun st ctxt src -> q (UItem v st) ctxt src) st ctxt src))
let wp_Dip_body c q v st ctxt src = ()

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
       st <-- forall_intro; ctxt <-- forall_intro; src <-- forall_intro; f <-- forall_intro;
       cases_stack (pack (Tv_Var st));;
       (**) smt;;
       (**) mapply (quote triple_Dip_aux);;
            mapply (quote wp_correct);;
            norm [delta_only ["Tezos.Hoare.op_Equals_Equals_Equals_Greater"]];;
            st' <-- forall_intro; ctxt' <-- forall_intro; src <-- forall_intro; h <-- implies_intro;
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

module S = Tezos.ScriptRepr

let toy_lambda = Dup >> Mul_intint
let toy_stack = UItem (DInt 3) (UItem (DLambda (Lam Int_t Int_t toy_lambda (S.String ""))) UEmpty)

val toy_p : assertion
let toy_p st ctxt src = 
  st == UItem (DInt 3) (UItem (DLambda (Lam Int_t Int_t (Seq Dup Mul_intint) (S.String ""))) UEmpty)

val toy_q : assertion
let toy_q st ctxt src = st == UItem (DInt 9) UEmpty

val toy_correct: st:stack -> ctxt:context -> src:contract -> f:nat -> 
  Lemma (spec Exec toy_p toy_q st ctxt src f)
let toy_correct st ctxt src f =
 match st with
   | UItem (DInt 3) (UItem (DLambda (Lam Int_t Int_t (Seq Dup Mul_intint) (S.String ""))) UEmpty) ->
     assert_by_tactic
       (spec Exec toy_p toy_q (UItem (DInt 3) (UItem (DLambda (Lam Int_t Int_t toy_lambda (S.String ""))) UEmpty))  ctxt src f)
       (apply_lemma (quote (triple_Exec_aux toy_p toy_q));;
        norm [primops];; split;; smt;;
        by_wp)
   | _ -> ()


/// Simple no-op program

let prog = Dup >> Drop

val prog_triple: st0:stack ->
  Lemma (triple prog (fun st ctxt src -> st == st0) (fun st ctxt src -> st == st0))
let prog_triple st0 =
  assert_by_tactic (triple prog (fun st ctxt src -> st == st0) (fun st ctxt src -> st == st0)) by_wp


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
let inv m st ctxt src =
  match st with
  | UItem (DBool b) (UItem (DInt n) (UItem (DInt acc) _)) ->
    b == (n <> 0) /\ 0 <= n /\ fact n * acc == fact m
  | _ -> False

val post: nat -> assertion
let post m st ctxt src =
  match st with
  | UItem (DInt n) (UItem (DInt acc) _) ->
    n == 0 /\ 1 * acc == fact m // Yes, the `1 *` is needed
  | _ -> False

(** When entered, [loop] restablishes the invariant:
 *  {fun st -> inv m [true;st]} loop {inv},
 * put otherwise
 *  [inv [true;st] ==> wp loop inv st
 *)
private val wp_loop_inv_true_: m:nat -> st:stack -> ctxt:context -> src:contract -> Lemma
  (requires inv m (UItem (DBool true) st) ctxt src)
  (ensures  wp loop (inv m) st ctxt src)
let wp_loop_inv_true_ m st ctxt src =
  match st with
  | UItem (DInt n) (UItem (DInt acc) rest) ->
    assert (0 <= n - 1 /\ fact (n - 1) * (n * acc) == fact m);
    assert_norm (wp loop (inv m) (UItem (DInt n) (UItem (DInt acc) rest)) ctxt src)
  | _ -> ()

let forall_intro_3 (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#p:(x:a -> y:b x -> z:c x y -> Type0))
		  ($f: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y). p x y z) = fun x -> Classical.forall_intro_2 (f x) in
    Classical.forall_intro g


//#set-options "--initial_fuel 7 --max_fuel 7 --initial_ifuel 5 --max_ifuel 5"
private val wp_loop_inv_true: m:nat -> Lemma
  ((fun st -> inv m (UItem (DBool true) st)) ===> wp loop (inv m))
let wp_loop_inv_true m = 
  assert_by_tactic ((fun st -> inv m (UItem (DBool true) st)) ===> wp loop (inv m))
    (norm [delta_only ["Tezos.Hoare.op_Equals_Equals_Equals_Greater"]];;
     st <-- forall_intro; ctxt <-- forall_intro; f <-- forall_intro; h <-- implies_intro;
     mapply (quote (wp_loop_inv_true_ m)))
     
(** [inv [false;st] ==> post st *)
private val wp_loop_inv_false: m:nat -> Lemma
  ((fun st -> inv m (UItem (DBool false) st)) ===> post m)
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
let p m st ctxt src =
  match st with
  | UItem (DInt n) _ -> n == m
  | _ -> True

val q: nat -> assertion
let q m st ctxt src =
  match st with
  | UItem (DInt acc) _ -> acc == fact m
  | _ -> False

val r: nat -> assertion
let r m st ctxt src = 
  match st with
  | UItem (DBool b) (UItem (DInt n) _) -> b == (m = 0) /\ n == m
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
