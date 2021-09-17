module Tezos.TypedExamples

open Tezos.Definitions
open Tezos.LanguageGadt

/// Factorial Contract

val factorial : instr (Item_t Int_t Empty_t) (Item_t Int_t Empty_t)

let factorial =
  (* [ n ] -- input parameter, n >= 0 *)
  Dup >>
  (* [ n ; n ] *)
  Eq >>
  (* [ (n = 0)? ; n ] *)
  If ( Drop >>
	(* [] *)
	Const_int 1
	(* [ 1 ] *) )        (* return 0! = 1 *)
      ( Const_int 1 >>    (* push accumulator's initial value *)
	(* [ acc ; n ] *)    (* acc = 1, n <> 0 *)
	Swap >>
	(* [ n ; acc ] *)
	Dup >>
	(* [ n ; n ; acc ] *)
	Neq >>
	(* [ (n <> 0)? ; n; acc ] *)
	Loop (
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
	  Neq
	  (* [ (n-1 <> 0)? ; n-1 ; n * acc ] *)
	) >>
	(* [ 0 ; acc ] *)
	Drop
	(* [ acc ] *) )

let v = step 30 factorial (Item 1 Empty)

val fact3 : unit -> Lemma (match step 30 factorial (Item 1 Empty) with | Partial _ (Item #s v st) -> s = Int_t /\ v == 1 | _ -> true)

let fact3 () = assert_norm (match step 30 factorial (Item 1 Empty) with | Partial _ (Item v st) -> v == 1 | _ -> true)

let rec fact (n : nat) : Tot int =
  if n = 0 then 1 else FStar.Mul.(n * (fact (n - 1)))

let loop_part =		(* [ (n <> 0)? ; n; acc ] *)
	Loop (
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
	  Neq
	  (* [ (n-1 <> 0)? ; n-1 ; n * acc ] *)
	)

// val factn : n:nat -> Lemma
//  (forall f.
//     match step f factorial (Item #Int_t (n<:int) Empty) with
//     | Partial _ (Item v _) -> v == fact n
//     | _ -> True)

let main =
  print_partial v;
  IO.print_string "\n"


/// Multisig contract

let lambda_input_type =
  Pair_t (Pair_t String_t Signature_t)
	 (Pair_t
	   (Pair_t (Map_t String_key Key_t) String_t)
	   Int_t)

let lambda_output_type =
  Pair_t (Pair_t (Map_t String_key Key_t) String_t)
	 Int_t

let lambda =
  Dup >> Cdr >> Swap >> Car >>
  Dup >> Cdr >> Swap >> Car >>
  diip ( Dup >> Cdr >> Swap >> Car ) >>
  diip ( Dup >> Cdr >> Swap >> Car ) >> Swap >>
  Dip
      ( Dip ( Dup ) >> Get >>
	If_none ( Fail ) ( Nop )
      ) >>
  diip ( Swap >> Dup ) >>
  diiip ( Swap >> Pair >> Swap ) >>
  Swap >> Dip ( Pair )  >>
  Check_signature >>
  If ( Const_int 1 >> Add_intint ) ( Fail ) >>
  Swap >> Pair

let ifcmpge (#cty : comparable_ty) #resty bt bf = ((Compare #cty #resty) >> Ge >> If bt bf)

let multisig_storage_type =
  Pair_t (Map_t String_key Key_t) Int_t

let multisig_param_type =
  Pair_t (Pair_t (Contract_t Unit_t Unit_t) Tez_t)
	 (Map_t String_key Signature_t)

let multisig_input_type =
  Item_t (Pair_t (Pair_t Tez_t multisig_param_type) multisig_storage_type) Empty_t

let multisig_output_type =
  Item_t (Pair_t Unit_t multisig_storage_type) Empty_t

let st =
  Item_t String_t
    (Item_t (Pair_t (Contract_t Unit_t
		Unit_t)
	    Tez_t)
	(Item_t (Map_t String_key Signature_t)
	    (Item_t (Map_t String_key Key_t)
		(Item_t Int_t
		    (Item_t (Pair_t (Pair_t Tez_t
				(Pair_t (Pair_t (Contract_t Unit_t
					    Unit_t)
					Tez_t)
				    (Map_t String_key Signature_t)
				))
			    (Pair_t (Map_t String_key
				    Key_t)
				Int_t))
			Empty_t)))))

#set-options "--max_fuel 6"
let duuuuuup = dup_rec #st 6

let t =
  Pair_t Tez_t
	 (Pair_t (Pair_t (Contract_t Unit_t Unit_t) Tez_t)
		 (Map_t String_key Signature_t))

/// Finally, the multisig contract itself

let multisig : instr multisig_input_type multisig_output_type =
  Dup >> Dup >> Cdr >> Swap >> cadr >> Dip ( Dup ) >>
  Dip ( Cdr >> Swap >> Car ) >>
  Dup >> Cdr >> Swap >> Car >>
  Dup >> Hash >>
  duuuuuup >> cdar #t #_ #Int_t #st >> Pair >>
  Const_int 0 >> Swap >> Pair >>
  Dip ( Swap ) >> Swap >>
  Lambda (ScriptRepr.String "Placeholder") lambda >>
  Map_reduce >>
  Cdr >> Dip ( Swap >> Drop >> Swap ) >>
  (ifcmpge #_ #Int_key) ( Dup >> Cdr >> Swap >> Car >> Unit >> Dip ( Swap ) >> diiip ( Cdr ) >>
	    Transfer_tokens #Unit_t #_ #_ #multisig_storage_type >> Pair )
	  ( Fail )
