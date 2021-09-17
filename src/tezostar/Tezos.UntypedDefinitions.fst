module Tezos.UntypedDefinitions

open Tezos.Primitives
open Tezos.Definitions
open Tezos.ScriptRepr
open Tezos.TezRepr

type lambda =
  | Lam: targ:ty -> tres:ty -> code:uinstr -> expr -> lambda

and uinstr =
  | Drop
  | Dup
  | Swap
  (* Constants; specialized to a few types *)
  | Const_int of int
  | Const_nat of nat
  | Const_bool of bool
  | Const_tez of tez
  | Const_string of string
  | Const_unit
  (* Pairs *)
  | Cons_pair
  | Car
  | Cdr
  (* Options *)
  | Cons_some
  | Cons_none of ty
  | If_none : uinstr -> uinstr -> uinstr
  (* Unions *)
  | Left
  | Right
  | If_left : uinstr -> uinstr -> uinstr
  (* Lists *)
  | Cons_list
  | Nill of ty // Nill instead of Nil; FStar extracts to the empty list otherwise
  | If_cons : uinstr -> uinstr -> uinstr
  | List_map
  | List_reduce
  (* Sets *)
  | Empty_set of comparable_ty
  | Set_map of comparable_ty
  | Set_reduce
  | Set_mem
  | Set_update
  | Set_size
  (* Maps *)
  | Empty_map : comparable_ty -> tagged_data -> uinstr
  | Map_map
  | Map_reduce
  | Map_mem
  | Map_get
  | Map_update
  | Map_size
  (* String operations *)
  | Concat
  (* Timestamp operations *)
  (* TODO[TZ]: check if we need int instead of nat *)
  | Add_seconds_to_timestamp
  | Add_timestamp_to_seconds
  (* Currency operations *)
  (* TODO[TZ]: we can either just have conversions to/from integers and
     do all operations on integers, or we need more operations on
     Tez. Also Sub_tez should return Tez.t option (if negative) and *)
  | Add_tez
  | Sub_tez
  | Mul_teznat
  | Mul_nattez
  | Ediv_teznat
  | Ediv_tez
  (* Boolean operations *)
  | Or
  | And
  | Xor
  | Not
  (* Integer operations *)
  | Neg_nat
  | Neg_int
  | Abs_int
  | Int_nat
  | Add_intint
  | Add_intnat
  | Add_natint
  | Add_natnat
  | Sub_int
  | Mul_intint
  | Mul_intnat
  | Mul_natint
  | Mul_natnat
  | Ediv_intint
  | Ediv_intnat
  | Ediv_natint
  | Ediv_natnat
  | Lsl_nat
  | Lsr_nat
  | Or_nat
  | And_nat
  | Xor_nat
  | Not_nat
  | Not_int
  (* Control *)
  | Seq : uinstr -> uinstr -> uinstr
  | If : uinstr -> uinstr -> uinstr
  | Loop of uinstr
  | Dip of uinstr
  | Exec
  | Lambda of lambda
  | Fail
  | Nop
  (* Comparison *)
  | Compare of comparable_ty
  (* Comparators *)
  | Eq
  | Neq
  | Lt
  | Gt
  | Le
  | Ge
   (* Protocol *)
  | Manager
  | Transfer_tokens of ty
  | Create_account
  | Default_account
  | Create_contract
  | Now
  | Balance
  | Check_signature
  | Hash_key
  | H of ty
  | Steps_to_quota (* TODO[TZ]: check that it always returns a nat *)
  | Source : ty -> ty -> uinstr
  | Amount

and tagged_data =
  | DInt of int
  | Nat of nat
  | DUnit
  | DBool of bool
  | DString of string
  | DKey of key
  | DKey_hash of pkeyhash
  | DSignature of signature
  | Timestamp of timestamp
  | DTez of tez
  | DPair : tagged_data -> tagged_data -> tagged_data
  | DMap of (myMap tagged_data tagged_data)
  | DSet of (mySet tagged_data)
  | DLambda of lambda
  | DUnion of (union tagged_data tagged_data)
  | DOption of (option tagged_data)
  | DContract of typed_contract
  | DList of (list tagged_data)

let (>>) = Seq

val tagged_data_list_to_string: list tagged_data -> string
val tagged_data_to_string: tagged_data -> string

let rec tagged_data_list_to_string = function
| [] -> "\b"
| hd::tl -> (tagged_data_to_string hd) ^ ";" ^ (tagged_data_list_to_string tl)

and tagged_data_to_string = function
| DInt n -> "Int(" ^ (string_of_int n)^ ")"
| Nat n -> "Nat(" ^ (string_of_int n)^ ")"
| DUnit -> "()"
| DBool b -> if b then "true" else "false"
| DString s -> s
| DTez n -> "Tez(" ^ (string_of_int n) ^ ")"
| DPair a b -> "Pair(" ^ (tagged_data_to_string a) ^ "," ^ (tagged_data_to_string b) ^ ")"
| DOption None -> "None"
| DOption (Some x) -> "Some(" ^ (tagged_data_to_string x) ^ ")"
| DList l -> "[" ^ (tagged_data_list_to_string l) ^ "]"
| _ -> "UnimplementedShow:<x:tagged_data>"

val instr_to_string: ui:uinstr -> string

let rec instr_to_string = function
  | Drop -> "DROP"
  | Dup -> "DUP"
  | Swap -> "SWAP"
  (* Constants; specialized to a few types *)
  | Const_int _ -> "PUSH int"
  | Const_bool _ -> "PUSH bool"
  | Const_tez _ -> "PUSH tez"
  | Const_string _ -> "PUSH string"
  | Const_unit -> "PUSH unit"
  (* Pairs *)
  | Cons_pair -> "PAIR"
  | Car -> "CAR"
  | Cdr -> "CDR"
  (* Options *)
  | Cons_some -> "SOME"
  | Cons_none _ -> "NONE"
  | If_none a b -> "IF_NONE {\n\t" ^ (instr_to_string a) ^ "}\n\t{" ^ (instr_to_string b) ^ "}"
  (* Unions *)
  | Left -> "LEFT"
  | Right -> "RIGHT"
  | If_left a b -> "IF_LEFT {\n\t" ^ (instr_to_string a) ^ "}\n\t{" ^ (instr_to_string b) ^ "}"
  (* Lists *)
  | Cons_list -> "LIST"
  | Nill _ -> "NIL"
  | If_cons a b -> "IF_CONS {\n\t" ^ (instr_to_string a) ^ "}\n\t{" ^ (instr_to_string b) ^ "}"
  | List_map -> "LIST_MAP"
  | List_reduce -> "LIST_REDUCE"
  (* Sets *)
  | Empty_set _ -> "EMPTY_SET"
  | Set_map _ -> "SET_MAP"
  | Set_reduce -> "SET_REDUCE"
  | Set_mem -> "SET_MEM"
  | Set_update -> "SET_UPDATE"
  | Set_size -> "SET_SIZE"
  (* Maps *)
  | Empty_map _ _ -> "EMPTY_MAP"
  | Map_map -> "MAP_MAP"
  | Map_reduce -> "MAP_REDUCE"
  | Map_mem -> "MAM_MEM"
  | Map_get -> "MAP_GET"
  | Map_update -> "MAP_UPDATE"
  | Map_size -> "MAP_SIZE"
  (* String operations *)
  | Concat -> "CONCAT"
  (* Timestamp operations *)
  (* TODO[TZ]: check if we need int instead of nat *)
  | Add_seconds_to_timestamp -> "ADD_SECONDS_TO_TIMESTAMP"
  | Add_timestamp_to_seconds -> "ADD_TIMESTAMP_TO_SECONDS"
  (* Currency operations *)
  (* TODO[TZ]: we can either just have conversions to/from integers and
     do all operations on integers, or we need more operations on
     Tez. Also Sub_tez should return Tez.t option (if negative) and *)
  | Add_tez -> "ADD_TEZ"
  | Sub_tez -> "SUB_TEZ"
  | Mul_teznat -> "MUL_TEZNAT"
  | Mul_nattez -> "MUL_NATTEZ"
  | Ediv_teznat -> "EDIV_TEZNAT"
  | Ediv_tez -> "EDIV_TEZ"
  (* Boolean operations *)
  | Or -> "OR"
  | And -> "AND"
  | Xor -> "XOR"
  | Not -> "NOT"
  (* Integer operations *)
  | Neg_nat -> "NEG nat"
  | Neg_int -> "NEG int"
  | Abs_int -> "ABS int"
  | Int_nat -> "INT"
  | Add_intint -> "ADD_INTINT"
  | Add_intnat -> "Add_INTNAT"
  | Add_natint -> "Add_NATINT"
  | Add_natnat -> "Add_NATNAT"
  | Sub_int -> "SUB_INT"
  | Mul_intint -> "MUL_INTINT"
  | Mul_intnat -> "MUL_INTNAT"
  | Mul_natint -> "MUL_NATINT"
  | Mul_natnat -> "MUL_NATNAT"
  | Ediv_intint -> "EDIV_INTINT"
  | Ediv_intnat -> "EDIV_INTNAT"
  | Ediv_natint -> "EDIV_NATINT"
  | Ediv_natnat -> "EDIV_NATNAt"
  | Lsl_nat -> "LSL nat"
  | Lsr_nat -> "LSR nat"
  | Or_nat -> "OR nat"
  | And_nat -> "AND nat"
  | Xor_nat -> "XOR nat"
  | Not_nat -> "NOT nat"
  | Not_int -> "NOT INT"
  (* Control *)
  | Seq a b -> (instr_to_string a) ^ "; " ^ (instr_to_string b)
  | If  a b -> "IF {\n\t" ^ (instr_to_string a) ^ "}\n\t{" ^ (instr_to_string b) ^ "}"
  | Loop a -> "LOOP {" ^ (instr_to_string a) ^ "}\n"
  | Dip a -> "DIP { " ^ (instr_to_string a) ^ "}\n"
  | Exec -> "EXEC"
  | Lambda _ -> "LAMBDA"
  | Fail -> "FAIL"
  | Nop -> "NOP"
  (* Comparison *)
  | Compare k -> "COMPARE " ^ (string_of_key k)
  (* Comparators *)
  | Eq -> "EQ"
  | Neq -> "NEQ"
  | Lt -> "LT"
  | Gt -> "GT"
  | Le -> "LE"
  | Ge -> "GE"
   (* Protocol *)
  | Manager -> "MANAGER"
  | Transfer_tokens _ -> "TRANSFER_TOKENS"
  | Create_account -> "CREATE_ACCOUNT"
  | Default_account -> "DEFAULT_ACCOUNT"
  | Create_contract -> "CREATE_CONTRACT"
  | Now -> "NOW"
  | Balance -> "BALANCE"
  | Check_signature -> "CHECK_SIGNATURE"
  | Hash_key -> "HASH_KEY"
  | H _ -> "HASH"
  | Steps_to_quota -> "STEPS_TO_QUOTA"
  | Source _ _ -> "SOURCE"
  | Amount -> "AMOUNT"
  | _ -> "<UNKNOWN OPCODE>"
