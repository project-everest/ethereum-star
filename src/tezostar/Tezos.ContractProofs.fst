module Tezos.ContractProofs

// open Tezos.Primitives
open Tezos.Definitions
open Tezos.UntypedExamples
open Tezos.Hoare

val anyone_correct : (kh : keyhash) ->
  Lemma (triple anyone_contract (fun st -> True) (fun st -> True))

let anyone_correct kh = ()
