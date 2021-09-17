module Tezos.Examples.Lambda

open FStar.Tactics

open Tezos.Definitions
open Tezos.UntypedDefinitions
open Tezos.AbstractInterpreter
open Tezos.Hoare


let p = (fun st -> st ==
  UItem (DInt 3)
        (UItem (DLambda Int_t Int_t (String "") (Dup >> Mul_intint)) UEmpty))

let q = (fun st -> st == UItem (DInt 9) UEmpty)

val aux: st:stack -> Lemma
 ((match st with
   | UItem arg UEmpty -> arg == DInt 3
   | _ -> True) ==>
  (match st with
   | UItem v st' ->
     wp Mul_intint
        (function
         | UItem (DInt 9) UEmpty -> True
         | _ -> False)
        (UItem v (UItem v st'))
    | _ -> True))
let aux st =
  match st with
  | UItem (DInt 3) UEmpty -> ()
  | UItem arg st -> admit()
  | _ -> ()



val triple_Exec_aux: p:assertion -> q:assertion -> st:stack -> f:nat -> Lemma
  (requires (match st with
	     | UItem arg (UItem (DLambda ta tb e ui) rest) ->
	       let u x = p (UItem x (UItem (DLambda ta tb e ui) rest)) in
	       let v y = q (UItem y (rest)) in
	       let u' stx = match stx with
	         	     | UItem arg' UEmpty -> (u arg /\ arg == arg')
	         	     | _ -> True in
	       let v' sty = match sty with
	         	     | UItem res UEmpty -> v res
	         	     | _ -> False in
	       spec ui u' v' st f
	     | _ -> True))
(ensures spec Exec p q st f)


val test: st:stack -> f:nat -> Lemma (spec Exec p q st f)
let test st f =
  match st with
  | UItem arg (UItem (DLambda Int_t Int_t (String "") (Seq Dup Mul_intint)) UEmpty) ->
    assert_by_tactic (spec Exec p q st f)
      (mapply (quote (triple_Exec_aux p q));;
       rewrite_equality (quote st);;
       mapply (quote wp_correct);;
      // norm [delta];;
     //  st <-- forall_intro;
       fail "end")
      // smt)
  | _ -> ()
