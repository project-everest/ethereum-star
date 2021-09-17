module Tezos.LanguageGadt

open FStar.IO
open FStar.ST
open Tezos.Primitives
open Tezos.Definitions
open Tezos.TezRepr
open Tezos.ScriptRepr

type hashT = | H : string -> hashT
type string_or_hash = | Sstring : string -> string_or_hash | Shash : hashT -> string_or_hash
type key = | K : string -> key
type signature = | Sign : key -> string_or_hash -> signature


type instr : stack_ty -> stack_ty -> Type =
  | Fail    : #bef:stack_ty -> #aft:stack_ty -> instr bef aft
  | Nop     : #bef:stack_ty -> instr bef bef
  | Seq     : #bef:stack_ty -> #trans:stack_ty -> #aft:stack_ty -> c1:instr bef trans -> c2:instr trans aft -> instr bef aft
  | If      : #t1:stack_ty -> #t2:stack_ty -> bt:instr t1 t2 -> bf:instr t1 t2 -> instr (Item_t Bool_t t1) t2
  | If_none : #ta:ty -> #tb:ty -> #t1:stack_ty -> #t2:stack_ty -> bt:instr t1 (Item_t tb t2) -> bf:instr (Item_t ta t1) (Item_t tb t2) -> instr (Item_t (Option_t ta) t1) (Item_t tb t2)
  | Dip     : #top:ty -> #bef:stack_ty -> #aft:stack_ty -> c:instr bef aft -> instr (Item_t top bef) (Item_t top aft)
  | Loop    : #rest:stack_ty -> instr rest (Item_t Bool_t rest) -> instr (Item_t Bool_t rest) rest
  | Drop    : #a:ty -> #rest:stack_ty -> instr (Item_t a rest) rest
  | Dup     : #a:ty -> #rest:stack_ty -> instr (Item_t a rest) (Item_t a (Item_t a rest))
  | Swap    : #a:ty -> #b:ty -> #rest:stack_ty -> instr (Item_t a (Item_t b rest)) (Item_t b (Item_t a rest))
  | Unit : #resty : stack_ty -> instr resty (Item_t Unit_t resty)
  | Const_int : #resty : stack_ty -> i:int -> instr resty (Item_t Int_t resty)
//  | Const   : #a:ty -> #rest:stack_ty -> #t:Type0{t == interp_ty a} -> v:t -> instr rest (Item_t a rest)
  | Car     : #a:ty -> #b:ty -> #rest:stack_ty -> instr (Item_t (Pair_t a b) rest) (Item_t a rest)
  | Cdr     : #a:ty -> #b:ty -> #rest:stack_ty -> instr (Item_t (Pair_t a b) rest) (Item_t b rest)
  | Pair    : #a:ty -> #b:ty -> #rest:stack_ty -> instr (Item_t a (Item_t b rest)) (Item_t (Pair_t a b) rest)
  | Or      : #rest:stack_ty -> instr (Item_t Bool_t (Item_t Bool_t rest)) (Item_t Bool_t rest)
  | And     : #rest:stack_ty -> instr (Item_t Bool_t (Item_t Bool_t rest)) (Item_t Bool_t rest)
  | Mul_intint : #rest:stack_ty -> instr (Item_t Int_t (Item_t Int_t rest)) (Item_t Int_t rest)
  | Add_intint : #rest:stack_ty -> instr (Item_t Int_t (Item_t Int_t rest)) (Item_t Int_t rest)
  | Sub_int : #rest:stack_ty -> instr (Item_t Int_t (Item_t Int_t rest)) (Item_t Int_t rest)
  | Eq      : #rest:stack_ty -> instr ((Item_t Int_t rest)) (Item_t Bool_t rest)
  | Ge      : #rest:stack_ty -> instr ((Item_t Int_t rest)) (Item_t Bool_t rest)
  | Neq     : #rest:stack_ty -> instr ((Item_t Int_t rest)) (Item_t Bool_t rest)
  | Hash    : #tt:ty -> #rest:stack_ty -> instr (Item_t tt rest) (Item_t String_t rest)
  | Check_signature : #rest:stack_ty -> instr (Item_t Key_t (Item_t (Pair_t Signature_t String_t) rest)) (Item_t Bool_t rest)
  | Get     : #tk:comparable_ty(*{comparable ty}*) -> #tv:ty -> #rest:stack_ty -> instr (Item_t (ty_of_comp_ty tk) (Item_t (Map_t tk tv) rest)) (Item_t (Option_t tv) rest)
  | Compare : #t:comparable_ty -> #rest:stack_ty -> instr (Item_t (ty_of_comp_ty t) (Item_t (ty_of_comp_ty t) rest)) (Item_t Int_t rest)
  | Lambda  : #arg:ty -> #ret:ty -> #bef:stack_ty -> expr -> code:instr (Item_t arg Empty_t) (Item_t ret Empty_t) -> instr bef (Item_t (Lambda_t arg ret) bef)
  | Map_reduce : #ta : comparable_ty -> #tv : ty -> #res : ty -> #rest : stack_ty -> instr (Item_t (Lambda_t (Pair_t (Pair_t (ty_of_comp_ty ta) tv) res) res) (Item_t (Map_t ta tv) (Item_t res rest)) ) (Item_t res rest)
  | Transfer_tokens : #p : ty -> #targ : ty -> #tret : ty -> #tsto : ty -> instr (Item_t targ (Item_t Tez_t (Item_t (Contract_t targ tret) (Item_t tsto Empty_t)))) (Item_t (tret) (Item_t tsto Empty_t))


val interp_ty : t : ty -> Type0

let rec interp_ty (t:ty) =
  match t with
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
    let a = interp_ty ta in
    let b = interp_ty tb in
    a * b
  | Union_t ta tb ->
    let a = interp_ty ta in
    let b = interp_ty tb in
    either a b
  | Map_t tk tv ->
    let k = interp_comp_ty tk in
    let v = interp_ty tv in
    myMap k v
  | Set_t tk ->
    let k = interp_comp_ty tk in
    mySet k
  | Option_t tv ->
    let v = interp_ty tv in
    option v
  | Lambda_t ta tb ->
    let a = interp_ty ta in
    let b = interp_ty tb in
    instr (stackify ta) (stackify tb)
  | Contract_t targ tret ->
    let a = interp_ty targ in
    let b = interp_ty tret in
    instr (stackify targ) (stackify tret)
  | List_t ta ->
    let a = interp_ty ta in
    list a

assume val compare_int : i1:int -> i2:int -> int // does Pervasives.Compare exist in FStar?
assume val hash : #t:ty -> #it:Type{it == interp_ty t} -> x:it -> string
assume val check_signature : k:key -> sign:signature -> str:string -> bool

assume val get : #tk:comparable_ty(*{comparable tk}*) -> #tv:ty -> #itk:Type{itk == interp_comp_ty tk} ->
  (let k = interp_comp_ty tk in
   let v = interp_ty tv in
   myMap k v -> itk -> option v)

noeq type stack : stack_ty -> Type =
| Item  : #t:ty -> #trest:stack_ty -> #it:Type{it == interp_ty t} -> x:it -> rest:stack trest -> stack (Item_t t trest)
| Empty : stack Empty_t

noeq type result : stack_ty -> Type =
| Failed    : #interm:stack_ty -> #bef:stack_ty -> #aft:stack_ty -> instr bef aft -> result interm
| Partial   : #aft:stack_ty -> fuel:nat -> stack aft -> result aft
| OutofFuel : #cur:stack_ty -> #target:stack_ty -> stack cur -> result target

#set-options "--z3rlimit 50 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 1"

val step : #a:stack_ty -> #b:stack_ty -> fuel:nat -> i:instr a b -> stack a -> Tot (result b) (decreases fuel)

let rec step #a #b fuel i st =
  match fuel with
  | 0 -> OutofFuel st
  | _ ->
  match i with
   | Drop ->
     let Item _ rest = st in
     Partial (fuel - 1) rest
   | Dup ->
     let Item #tv v rest = st in
     Partial (fuel - 1) (Item #tv v st)
   | Swap ->
     let Item #t1 v1 (Item #t2 v2 rest) = st in
     Partial (fuel - 1) (Item #t2 v2 (Item #t1 v1 rest))
   | Const_int v ->
     Partial (fuel - 1) (Item #Int_t v st)
   | Car ->
     let Item #tu u rest = st in
     let Pair_t ta tb = tu in
     Partial (fuel - 1) (Item #ta (fst #(interp_ty ta) #(interp_ty tb) u) rest)
   | Cdr ->
     let Item #tu u rest = st in
     let Pair_t ta tb = tu in
     Partial (fuel - 1) (Item #tb (snd #(interp_ty ta) #(interp_ty tb) u) rest)
   | Pair ->
     let Item #t1 v1 (Item #t2 v2 rest) = st in
     Partial (fuel - 1) (Item #(Pair_t t1 t2) (v1, v2) rest)
   | Or ->
     let Item v1 (Item v2 rest) = st in
     Partial (fuel - 1) (Item #Bool_t (v1 || v2) rest)
   | And ->
     let Item v1 (Item v2 rest) = st in
     Partial (fuel - 1) (Item #Bool_t (v1 && v2) rest)
   // TODO: Integers are arbitrary precision, how much gas these consume?
   | Mul_intint ->
     let Item v1 (Item v2 rest) = st in
     Partial (fuel - 1) (Item #Int_t FStar.Mul.(v1 * v2) rest)
   | Add_intint ->
     let Item v1 (Item v2 rest) = st in
     Partial (fuel - 1) (Item #Int_t (v1 + v2) rest)
   | Sub_int ->
     let Item v1 (Item v2 rest) = st in
     Partial (fuel - 1) (Item #Int_t (v1 - v2) rest)
   | Compare -> // Only handling Int_t case
     let Item #t1 v1 (Item #t2 v2 rest) = st in
     begin
     match t1, t2 with
     | Int_t, Int_t -> Partial (fuel - 1) (Item #Int_t (compare_int v1 v2) rest)
     | _ -> Failed i
     end
   | Fail -> Failed (Fail #a #b)
   | Nop  -> Partial fuel st
   | Seq d1 d2 ->
     begin
     match step (fuel - 1) d1 st with
     | Failed i      -> Failed i
     | OutofFuel s   -> OutofFuel s
     | Partial f st' -> step (min f (fuel - 1)) d2 st'
     end
   | If bt bf ->
     let Item b rest = st in
     step (fuel - 1) (if b then bt else bf) rest
   | If_none bt bf ->
     let Item #to ov rest = st in
     let Option_t tv = to in
     let ov : option (interp_ty tv) = ov in
     begin
     match ov with
     | Some v -> step (fuel - 1) bf (Item #tv v rest)
     | None   -> step (fuel - 1) bt rest
     end
   | Dip c ->
     let Item #tv v rest = st in
     begin
     match step (fuel - 1) c rest with
     | Failed i      -> Failed i
     | OutofFuel s   -> OutofFuel s
     | Partial f st' -> Partial f (Item #tv v st')
     end
   | Loop body ->
     let Item b rest = st in
     if b then
       match step (fuel - 1) body rest with
       | Failed i      -> Failed i
       | OutofFuel s   -> OutofFuel s
       | Partial f st' ->
	 if 0 < f then step (min f (fuel - 1)) i st' else OutofFuel st'
     else Partial fuel rest
   | Eq ->
     let Item v rest = st in
     Partial fuel (Item #Bool_t (v = 0) rest)
   | Ge ->
     let Item v rest = st in
     Partial fuel (Item #Bool_t (v >= 0) rest)
   | Neq ->
     let Item v rest = st in
     Partial fuel (Item #Bool_t (v <> 0) rest)
   | Hash ->
     let Item #tv v rest = st in
     Partial fuel (Item #String_t (hash #tv v) rest)
   | Check_signature ->
     let Item k (Item p rest) = st in
     let sign, str : signature * string = p in
     Partial fuel (Item #Bool_t (check_signature k sign str) rest)
(* Can't get the two following opcodes to typecheck *)
   // | Get ->
   //   let Item_t tyk (Item_t (Map_t ctyk tv) resty) = a in
   //   let _ = assert(interp_ty (ty_of_comp_ty ctyk) == interp_comp_ty ctyk) in
   //   let Item #_ vk (Item #tm m rest) = st in
   //   Partial fuel (Item #(Option_t tv) (get #ctyk #tv m vk) rest)
   // | Map_reduce ->
   //   let (Item_t (Lambda_t (Pair_t (Pair_t tk tv) res) res)
   //     (Item_t (Map_t tk tv) (Item_t res rest)) ) = a in
   //   // let Item_t res resty = b in
   //   let ttv = interp_ty tv in
   //   let Item lam (Item (m : myMap key ttv) (Item init rest)) = st in
   //     let f (partial : result b) (k : key) (v : ttv) =
   //	 match partial with
   //	  | Failed i -> Failed i
   //	  | Partial f stp -> step (min f (fuel - 1)) lam stp
   //	  | OutofFuel st -> OutofFuel st in
   //     map_fold_left #(result b) key ttv m f (Partial fuel (Item init rest))
   | _ -> Failed i

val (>>) : #bef:stack_ty -> #trans:stack_ty -> #aft:stack_ty -> c1:instr bef trans -> c2:instr trans aft -> instr bef aft
let (>>) = Seq

let print_partial (v:result (Item_t Int_t Empty_t)) : All.ML unit =
 match v with
 | Partial _ (Item i Empty) -> FStar.IO.print_string (string_of_int i)
 | OutofFuel _ -> FStar.IO.print_string "Out of fuel\n"
 | Failed _ -> FStar.IO.print_string "Failed\n"

/// "Syntactic sugar" opcodes

let cadr #a #b #c #rest : instr (Item_t (Pair_t (Pair_t a b) c) rest) (Item_t b rest) = Car >> Cdr

let cdar #a #b #c #rest : instr (Item_t (Pair_t a (Pair_t b c)) rest) (Item_t b rest) = Cdr >> Car

let diip #top1 #top2 #a #b (i:instr a b) = Dip #top1 (Dip #top2 i)
let diiip #top1 #top2 #top3 #a #b (i:instr a b) = Dip #top1 (Dip #top2 (Dip #top3 i))
let diiiip #top1 #top2 #top3 #top4 #a #b (i:instr a b) = Dip #top1 (Dip #top2 (Dip #top3 (Dip #top4 i)))

val stack_depth: stack_ty -> nat
let rec stack_depth = function
 | Empty_t -> 0
 | Item_t _ st -> 1 + stack_depth st

let rec stack_ty_nth (st:stack_ty) (n:pos{stack_depth st >= n}) : ty =
 let Item_t t st' = st in
 match n with
 | 1 -> t
 | n -> stack_ty_nth st' (n-1)

val dup_rec: #st:stack_ty -> n:pos{stack_depth st >= n}
 -> instr st (Item_t (stack_ty_nth st n) st)
let rec dup_rec #st = function
 | 1 ->
   let Item_t t st' = st in
   Dup #t #st'
 | n ->
   let Item_t t st' = st in
   let t' = stack_ty_nth st' (n-1) in
   Dip #t #st' #(Item_t t' st') (dup_rec #st' (n-1)) >> Swap #t #t' #st'
