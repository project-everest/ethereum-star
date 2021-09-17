open Client_embedded_proto_alpha
open Client_alpha.Michelson_parser
open Script_ir_translator
open Tezos_ScriptRepr

(* open Tezos_embedded_protocol_alpha --> future versions of Tezos *)

type ocontext = Tezos_context.context

let ocontext0 = Obj.magic ()

(* this function should not be necessary, since they are the same type *)
let rec convert (e:Tezos_context.Script.expr) : Script_repr.expr =
  match e with
  | Int(a,b) -> Int(a,b)
  | String(a,b) -> String(a,b)
  | Prim(a,b,c,d) -> Prim(a,b,List.map convert c,d)
  | Seq(a,b,c) -> Seq(a,List.map convert b,c)

(* oexpr is for ocaml expr (ScriptRepr.expr), fexpr is for Fstar expr  *)
let rec to_tezos = function
  | Int s -> Script_repr.Int(-1, s)
  | String s -> Script_repr.String(-1,s)
  | Prim(s,l) -> Script_repr.Prim(-1,s,List.map to_tezos l,None)
  | Seq el -> Script_repr.Seq(-1,List.map to_tezos el,None)

let hash_expr (e:expr) = Script_repr.hash_expr (to_tezos e)

let rec of_tezos = function
  | Script_repr.Int(_,s) -> Int s
  | Script_repr.String(_,s) -> String s
  | Script_repr.Prim(_,s,l,_) -> Prim (s,List.map of_tezos l)
  | Script_repr.Seq(_,l,_) -> Seq (List.map of_tezos l)

let (>>=?) v f =
  match v with
  | Error _ as err -> err
  | Ok v -> f v

let int_of_string s =
  try Some (Z.of_string s) with _ -> None

let parse_data (s:string) : expr option =
 match Lwt_main.run (Client_alpha.Client_proto_programs.parse_data s) with
 | Ok {ast =e} -> Some (of_tezos (convert e))
 | Error e -> None

let parse_contract (ctxt:ocontext) (fileName:string) : (expr * expr * expr * expr) option =
  let code = Utils.read_file fileName in
  (* print_string ("Parsed code:\n "^code^".\n\n"); *)
  let parsed = Client_alpha.Client_proto_programs.parse_program code in
  match Lwt_main.run parsed with
  | Ok {ast={code;arg_type;ret_type;storage_type}} ->
   (* let bytes = Data_encoding.Binary.to_bytes Script_repr.expr_encoding (convert code) in print_string (MBytes.to_string bytes); *)
   let open Script_ir_translator in
   let open Script_typed_ir in begin
   match parse_ty arg_type,parse_ty ret_type,parse_ty storage_type with
    | Ok (Ex_ty arg_type'), Ok (Ex_ty ret_type'),Ok (Ex_ty storage_type') ->
        let arg_type_full = Pair_t (arg_type', storage_type') in
        let ret_type_full = Pair_t (ret_type', storage_type') in
        begin match Lwt_main.run (parse_lambda ~storage_type:storage_type' ctxt arg_type_full ret_type_full code) with
        | Ok (Lam(_,e)) -> ignore(e);
               Some(of_tezos (convert code),
                    of_tezos (convert arg_type),
                    of_tezos (convert ret_type),
                    of_tezos (convert storage_type))
        | _ -> None end
    | _ -> None end
     (* Ok (Some(code,arg_type,ret_type,storage_type)) *)
  | _ -> print_string ("Could not parse "^(fileName)^".\n"); None

let tez_of_string_as_int64 s =
  match (Tez_repr.of_string s) with
  | None -> None
  | Some v -> Some (Z.of_int (Int64.to_int (Tez_repr.to_int64 v)))
(* TSP: FIXME: This is not really satisfying.. We want more guarantees
about overflows and such *)
