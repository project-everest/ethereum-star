module Tezos.Test

open FStar.IO

open Tezos.Error
open Tezos.Primitives
open Tezos.Definitions
open Tezos.UntypedDefinitions
open Tezos.Serialization
open Tezos.Interpreter
open Tezos.Storage

module TT = Tezos.Translation
module SR = Tezos.ScriptRepr
module F = FStar_interface
module CI = CryptoInterface


assume val orig_nonce0: origination_nonce

assume val orig0: contract

val source0: contract
let source0 =
  let _, pkeyhash = CI.gen_keys "10" in
  Default pkeyhash

let qta0: quota = 1000

let amount0: tez = 100

let verbose = true

let print s = if verbose then print_string s else ()

let context1 =
  match update_contract_balance context0 source0 400000000 with
  | Ok context1 -> context1
  | Error e -> context0

(** The boolean [fails] means that we are asserting failure *)
val assert_output_aux: bool -> string -> string -> string -> string -> tzresult string
let assert_output_aux fails fileName sstorage sinput sexpectedOutput =
  match F.parse_contract F.ocontext0 fileName with
  | None -> return ("Parsing failed on file " ^ fileName)
  | Some (ecode,eargty,eretty,estoragety) ->
    (* obtain input type and input *)
    inty <-- TT.expr_to_ty eargty;
    match F.parse_data sinput with
    | None -> fail (GenericError ("Invalid input to contract" ^ fileName))
    | Some einput ->
      input <-- TT.expr_to_data context0 inty einput;
      (* obtain output type and output *)
      retty <-- TT.expr_to_ty eretty;
      match F.parse_data sexpectedOutput with
      | None -> fail (GenericError ("Invalid format for expected output in test for contract "^fileName^": "^sexpectedOutput^"\n"))
      | Some eexpectedOutput ->
        expectedOutput <-- TT.expr_to_data context0 retty eexpectedOutput;
        match F.parse_data sstorage with
        | None -> fail (GenericError ("Invalid storage in test for  contract"^fileName))
        | Some estorage ->
          stoty <-- TT.expr_to_ty estoragety;
          storage <-- TT.expr_to_data context0 stoty estorage;
          begin
          match TT.expr_to_instr context0 ecode (Item_t (Pair_t inty stoty) Empty_t) with
          | Ok (ui,_) ->
            let s1 = "Interpreting "^fileName^"..." in
            let res = interp orig_nonce0 qta0 orig0 source0 amount0 context1 ui (DPair input storage) in
            begin
            match res with
            | Ok (DPair y _, _ ,_ ,_) ->
              let s1 = s1 ^ (if fails then "[Asserting failure]" else "testing: ") in
              if fails then
                return ("This computation ("^(fileName)^") should have failed but it evaluated successfully and returned "^(tagged_data_to_string y)^"[FAILURE].\n")
              else
                let s2 =
                  if y <> expectedOutput then
                     ("Evaluation succeeded, but result is "
                     ^ (tagged_data_to_string y)
                     ^ " instead of "
                     ^ (tagged_data_to_string expectedOutput)^".\n")
                  else
                    "SUCCESS\n" in
                  return (s1 ^ s2)
            | Ok(y,_,_,_) ->
              let s2 = ("Error: the ouput is not a pair " ^ (tagged_data_to_string y)) in
              return (s1 ^ s2)
            | Error (Reject) -> return ("Contract "^(fileName)^" failed as expected: SUCCESS\n")
            | Error e ->
              let s2 = ("Error: "^(error_to_string e)^"\n") in
              let s3 = ("Evaluation failed on program:\n" ^ (SR.expr_to_string ecode) ^ "\n\n") in
              return (s1 ^ s2 ^ s3)
            end
          | Error e -> return ("Evaluation failed: " ^ (error_to_string e) ^ ".\n")
          end


val assert_output: string -> string -> string -> string -> All.ML unit
let assert_output fileName sstorage sinput sexpectedOutput =
  match assert_output_aux false ("contracts/" ^ fileName) sstorage sinput sexpectedOutput with
  | Ok s -> print_string s
  | Error e -> print_string (error_to_string e)


val assert_fails: string -> string -> string -> All.ML unit
let assert_fails fileName sstorage sinput   =
  match assert_output_aux true ("contracts/" ^ fileName) sstorage sinput "Unit" with
  | Ok s -> print_string s
  | Error e -> print_string ((error_to_string e)^"\n")

val go: unit -> All.ML unit
let go () =
  assert_output "ret_int.tz" "Unit" "Unit" "300";
/// Identity on strings
  assert_output "str_id.tz" "Unit" "\"Hello\"" "\"Hello\"";
  assert_output "str_id.tz" "Unit" "\"abcd\"" "\"abcd\"";
/// Identity on pairs
  assert_output "pair_id.tz" "Unit" "(Pair True False)" "(Pair True False)";
  assert_output "pair_id.tz" "Unit" "(Pair False True)" "(Pair False True)";
  assert_output "pair_id.tz" "Unit" "(Pair True True)" "(Pair True True)";
  assert_output "pair_id.tz" "Unit" "(Pair False False)" "(Pair False False)";
/// Logical not
  assert_output "not.tz" "Unit" "True" "False";
  assert_output "not.tz" "Unit" "False" "True";
/// Logical and
  assert_output "and.tz" "Unit" "(Pair False False)" "False";
  assert_output "and.tz" "Unit" "(Pair False True)" "False";
  assert_output "and.tz" "Unit" "(Pair True False)" "False";
  assert_output "and.tz" "Unit" "(Pair True True)" "True";
/// Logical or
  assert_output "or.tz" "Unit" "(Pair False False)" "False";
  assert_output "or.tz" "Unit" "(Pair False True)" "True";
  assert_output "or.tz" "Unit" "(Pair True False)" "True";
  assert_output "or.tz" "Unit" "(Pair True True)" "True";
/// XOR
  assert_output "xor.tz" "Unit" "(Pair False False)" "False";
  assert_output "xor.tz" "Unit" "(Pair False True)" "True";
  assert_output "xor.tz" "Unit" "(Pair True False)" "True";
  assert_output "xor.tz" "Unit" "(Pair True True)" "False";
/// Build list
  assert_output "build_list.tz" "Unit" "0" "(List 0)";
  assert_output "build_list.tz" "Unit" "3" "(List 0 1 2 3)";
  assert_output "build_list.tz" "Unit" "10" "(List 0 1 2 3 4 5 6 7 8 9 10)";
/// Concatenate all strings of a list into one string
  assert_output "concat_list.tz" "Unit" "(List \"a\" \"b\" \"c\")" "\"abc\"";
  assert_output "concat_list.tz" "Unit" "(List)" "\"\"";
  assert_output "concat_list.tz" "Unit"
    "(List \"Hello\" \" \" \"World\" \"!\")" "\"Hello World!\"";
/// Find maximum int in list -- returns None if not found
  assert_output "max_in_list.tz" "Unit" "(List)" "None";
  assert_output "max_in_list.tz" "Unit" "(List 1)" "(Some 1)";
  assert_output "max_in_list.tz" "Unit" "(List -1)" "(Some -1)";
  assert_output "max_in_list.tz" "Unit" "(List 10 -1 -20 100 0)" "(Some 100)";
  assert_output "max_in_list.tz" "Unit" "(List 10 -1 -20 100 0)" "(Some 100)";
  assert_output "max_in_list.tz" "Unit" "(List -10 -1 -20 -100)" "(Some -1)";
/// Identity on lists
  assert_output "list_id.tz" "Unit" "(List \"1\" \"2\" \"3\")" "(List \"1\" \"2\" \"3\")";
  assert_output "list_id.tz" "Unit" "(List)" "List";
  assert_output "list_id.tz" "Unit" "(List \"a\" \"b\" \"c\")" "(List \"a\" \"b\" \"c\")";

  assert_output "list_id_map.tz" "Unit" "(List \"1\" \"2\" \"3\")" "(List \"1\" \"2\" \"3\")";
  assert_output "list_id_map.tz" "Unit" "(List)" "List";
  assert_output "list_id_map.tz" "Unit" "(List \"a\" \"b\" \"c\")" "(List \"a\" \"b\" \"c\")";
/// Asserts
  assert_output "assert_eq.tz" "Unit" "(Pair -1 -1)" "Unit";
  assert_fails "assert_eq.tz" "Unit" "(Pair 0 -1)";

  assert_output "assert_eq.tz" "Unit" "(Pair -1 -1)" "Unit";
  assert_fails "assert_eq.tz"  "Unit" "(Pair 0 -1)";

  assert_output "assert_neq.tz" "Unit" "(Pair 0 -1)" "Unit";
  assert_fails "assert_neq.tz"  "Unit" "(Pair -1 -1)";

  assert_output "assert_lt.tz" "Unit" "(Pair -1 0)" "Unit";
  assert_fails "assert_lt.tz"  "Unit" "(Pair 0 -1)";
  assert_fails "assert_lt.tz"  "Unit" "(Pair 0 0)";

  assert_output "assert_le.tz" "Unit" "(Pair 0 0)" "Unit";
  assert_output "assert_le.tz" "Unit" "(Pair -1 0)" "Unit";
  assert_fails "assert_le.tz"  "Unit" "(Pair 0 -1)";

  assert_output "assert_gt.tz" "Unit" "(Pair 0 -1)" "Unit";
  assert_fails "assert_gt.tz"  "Unit" "(Pair -1 0)";
  assert_fails "assert_gt.tz"  "Unit" "(Pair 0 0)";

  assert_output "assert_ge.tz" "Unit" "(Pair 0 0)" "Unit";
  assert_output "assert_ge.tz" "Unit" "(Pair 0 -1)" "Unit";
  assert_fails "assert_ge.tz"  "Unit" "(Pair -1 0)";

  assert_output "assert_cmpeq.tz" "Unit" "(Pair -1 -1)" "Unit";
  assert_fails "assert_cmpeq.tz"  "Unit" "(Pair 0 -1)";

  assert_output "assert_cmpeq.tz" "Unit" "(Pair -1 -1)" "Unit";
  assert_fails "assert_cmpeq.tz"  "Unit" "(Pair 0 -1)";

  assert_output "assert_cmpneq.tz" "Unit" "(Pair 0 -1)" "Unit";
  assert_fails "assert_cmpneq.tz"  "Unit" "(Pair -1 -1)";

  assert_output "assert_cmplt.tz" "Unit" "(Pair -1 0)" "Unit";
  assert_fails "assert_cmplt.tz"  "Unit" "(Pair 0 -1)";
  assert_fails "assert_cmplt.tz"  "Unit" "(Pair 0 0)";

  assert_output "assert_cmple.tz" "Unit" "(Pair 0 0)" "Unit";
  assert_output "assert_cmple.tz" "Unit" "(Pair -1 0)" "Unit";
  assert_fails "assert_cmple.tz"  "Unit" "(Pair 0 -1)";

  assert_output "assert_cmpgt.tz" "Unit" "(Pair 0 -1)" "Unit";
  assert_fails "assert_cmpgt.tz"  "Unit" "(Pair -1 0)";
  assert_fails "assert_cmpgt.tz"  "Unit" "(Pair 0 0)";

  assert_output "assert_cmpge.tz" "Unit""(Pair 0 0)" "Unit";
  assert_output "assert_cmpge.tz" "Unit""(Pair 0 -1)" "Unit";
  assert_fails "assert_cmpge.tz"  "Unit" "(Pair -1 0)";
/// Signatures
  assert_output "check_signature.tz" "(Pair \"26981d372a7b3866621bf79713d249197fe6d518ef702fa65738e1715bde9da54df04fefbcc84287ecaa9f74ad9296462731aa24bbcece63c6bf73a8f5752309\" \"hello\")"
  "\"edpkuBknW28nW72KG6RoHtYW7p12T6GKc7nAbwYX5m8Wd9sDVC9yav\"" "True";

  assert_output "check_signature.tz" "(Pair \"26981d372a7b3866621bf79713d249197fe6d518ef702fa65738e1715bde9da54df04fefbcc84287ecaa9f74ad9296462731aa24bbcece63c6bf73a8f5752309\" \"abcd\")" "\"edpkuBknW28nW72KG6RoHtYW7p12T6GKc7nAbwYX5m8Wd9sDVC9yav\"" "False";
/// Hashing
  assert_output "hash_key.tz" "Unit" "\"edpkuBknW28nW72KG6RoHtYW7p12T6GKc7nAbwYX5m8Wd9sDVC9yav\"" "\"tz1KqTpEZ7Yob7QbPE4Hy4Wo8fHG8LhKxZSx\"";
  assert_output "hash_key.tz" "Unit" "\"edpkuJqtDcA2m2muMxViSM47MPsGQzmyjnNTawUPqR8vZTAMcx61ES\"" "\"tz1XPTDmvT3vVE5Uunngmixm7gj7zmdbPq6k\"";

  assert_output "hash_string.tz" "Unit" "\"abcdefg\"" "\"exprv3MnhXvjthGzZ7jDtXRRFremZyey9rsGtL7JRkeaQX1fThN7WF\"";
  assert_output "hash_string.tz" "Unit" "\"12345\"" "\"expru81QVHsW2qaWLNHnMHSxDNhqtat17ajadri6mKUvXyc2EWHZC3\"";

  assert_output "balance.tz" "Unit" "Unit" "\"4,000,000.00\""

let main = go ()
