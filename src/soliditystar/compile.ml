open Ast
open Globals
open Printf

module Smap = Map.Make(String)

type envt =
  | EnumConst
  | State
  | Local
  | MethodName

type env = envt Smap.t
type menv = function_t Smap.t

let w x = fprintf !output x
let pad = (fun n->String.make (!pad_len*n) ' ')

let contract_name: string ref = ref ""
let cons_allocs: string ref = ref ""

(* Extract a type following F* conventions *)
let rec ty b = function
  | Named x ->
     let x=BatString.uncapitalize x in
     if b then sprintf "ref %s" x else x
  | Mapping(x, t) -> sprintf "mapping %s (%s)" x (ty false t)
  | Array t -> sprintf "mapping uint (%s)" (ty false t)

let rec returns (strong:bool) (s:statement_t) =
   let (s,loc) = s in
   match s with
   | Return(_) -> true
   | Throw -> true
   | Block(sl) -> if strong then List.for_all (returns strong) sl else List.exists (returns strong) sl
   | If(e, s1, s2) ->
      let a, b = returns strong s1, (match s2 with None -> false | Some s -> returns strong s) in
      if strong then a && b else a || b
   | _ -> false

let ghetto_cps (sl:statement_t list) =
  let rec aux = function
    | [] -> []
    | h :: t ->
      let (s, loc) = h in
      (match s with
      | If(e, s, so) ->
        if returns true h then [h]
        else if so = None then [If(e, s, Some(Block(t),loc)),loc]
        else (
          let news = match s with
            | Block(bsl), loc -> Block(bsl @ t), loc
            | ss, loc -> Block((ss,loc) :: t), loc in
          let Some so = so in
          let newso = match so with
            | Block(bsl), loc -> Block(bsl @ t), loc
            | ss, loc -> Block((ss, loc) :: t), loc in
          [If(e, news, Some newso),loc]
        )
      | _ -> h :: (aux t))
  in aux sl

let rec compile_s (d:int) (env:env) (s:statement_t) =
  let cs = compile_s d env in
  let ce = compile_e d env in
  let (s, loc) = s in
  match s with
  | Empty | Block([]) -> (pad d) ^ "()"
  | Return(eo) -> sprintf "%s%s" (pad d) (match eo with None -> "()" | Some e -> ce e)
  | Throw -> sprintf "%sthrow ()" (pad d)
  | Block(sl) ->
     let sl = ghetto_cps sl in
     let sl = List.map cs sl in
     let folder acc s =
       if acc = "" then s
       else if BatString.ends_with acc " in" then acc ^ "\n" ^ (pad d) ^ s
       else acc ^ ";\n" ^ (pad d) ^ s in
     let composed = List.fold_left folder "" sl in
     if BatString.ends_with composed " in" then composed^"\n"^(pad d)^"()"
     else composed
  | Expression(e) -> (pad d) ^ (ce e)
  | Declaration(ty, tl) ->
     let l = List.map (fun (x,eo) -> sprintf "%slet %s : %s = %s in" (pad d) x ty (match eo with None -> "None" | Some e -> ce e)) tl in
     String.concat "\n" l
  | If(e, s, so) ->
    sprintf "%sif (%s) then\n%s\n%s" (pad d) (ce e) (compile_s (d+1) env s)
      (match so with None -> "" | Some s -> sprintf "%selse\n%s" (pad d) (compile_s (d+1) env s))
  | s -> failwith (sprintf "unsupported statement: %s" (Pretty.pretty_print_statement 0 (s,loc)))

and compile_e (d:int) (env:env) (e:expression_t) =
  let cs = compile_s d env in
  let ce = compile_e d env in
  let (e, loc) = e in
  match e with
  | This -> failwith "Unsupported this, can only be used to call local methods externally"
  | Null | Undefined | Elision -> failwith "null / undefined / elision"
  | Bool(b) -> if b then "true" else "false"
  | Number(n) -> let s = cutdot (sprintf "%F" n) in sprintf "to_uint %s" s
  | String(s) -> "\""^(recode_utf8 s)^"\""
  | Identifier(i) ->
     (try
       match Smap.find i env with
       | Local -> raise Not_found
       | State -> sprintf "store.%s" i
       | _ -> failwith "bad assign"
     with
     | _ -> sprintf "%s" i)
  | Dot(e,i) ->
     let se = ce e in
     (match i with
     | "send" -> sprintf "send (%s)" (ce e)
     | "balance" -> sprintf "balance (%s)" (ce e)
     | _ ->
       (match fst e with
       | Identifier(x) -> sprintf "%s.%s" (ce e) i
       | _ -> sprintf "(%s).%s" (ce e) i))
  | Property(e,f) -> sprintf "lookup (%s) (%s)" (ce e) (ce f)
  | Call(f, l) ->
      sprintf "%s %s" (ce f)
      (if l=[] then "()" else String.concat " " (List.map (fun x -> sprintf "(%s)" (ce x)) l))
  | Postincr(e) -> sprintf "add (%s) (one 256)" (ce e)
  | Postdecr(e) -> sprintf "add (%s) (one 256)" (ce e)
  | Minus(e) -> sprintf "neg (%s)" (ce e)
  | Lnot(e) -> sprintf "not (%s)" (ce e)
  | Mod(e,f) -> sprintf "mod (%s) (%s)" (ce e) (ce f)
  | Divide(e,f) -> sprintf "div (%s) (%s)" (ce e) (ce f)
  | Multiply(e,f) -> sprintf "mul (%s) (%s)" (ce e) (ce f)
  | Add(e,f) -> sprintf "add (%s) (%s)" (ce e) (ce f)
  | Sub(e,f) -> sprintf "sub (%s) (%s)" (ce e) (ce f)
  | Lt(e,f) -> sprintf "lt (%s) (%s)" (ce e) (ce f)
  | Gt(e,f) -> sprintf "gt (%s) (%s)" (ce e) (ce f)
  | Le(e,f) -> sprintf "le (%s) (%s)" (ce e) (ce f)
  | Ge(e,f) -> sprintf "ge (%s) (%s)" (ce e) (ce f)
  | Equal(e,f) -> sprintf "eq (%s) (%s)" (ce e) (ce f)
  | Land(e,f) -> sprintf "(%s) && (%s)" (ce e) (ce f)
  | Lor(e,f) -> sprintf "(%s) || (%s)" (ce e) (ce f)
  | Conditional(c,e,f) ->  sprintf "(if %s then %s else %s)" (ce c) (ce e) (ce f)
  | Assign(e,f) ->
      (match e with
      | Identifier(i), _ ->
        let cf = ce f in
        (try
          match Smap.find i env with
          | Local -> raise Not_found
          | State -> sprintf "update (store.%s) (%s)" i cf
          | _ -> failwith "bad assign"
        with
        | _ -> sprintf "let %s = %s in" i cf)
      | Dot(e, i), _ ->
        ce (Assign(e, (Identifier(sprintf "{%s with %s = %s}" (ce e) i (ce f)),loc)), loc)
      | Property(e, p), _ ->
        sprintf "update_map (%s) (%s) (%s)" (ce e) (ce p) (ce f)
      | _ -> sprintf "update (store.%s) (%s)" (ce e) (ce f))
  | Sequence(e) -> sprintf "(%s)" (String.concat ", " (List.map ce e))
  | _ -> failwith "bad expression"

(* Pseudo-map function on AST. Traverses the tree and calls basee / bases on leaves *)
let ast_map bases basee body =
  let rec applys ((s,loc):statement_t) : statement_t =
   let rs = match s with
   | Return eo -> Return (match eo with None -> None | Some e -> Some (applye e))
   | Block sl -> Block (List.map applys sl)
   | Expression e ->
     (match applys (Expression e, loc) with
     | (Expression f, _) when e=f -> Expression (applye e)
     | s, _ -> s)
   | Declaration(x, dl) -> Declaration(x,
      List.map (fun (k,eo) -> k, (match eo with None -> None | Some e -> Some (applye e))) dl)
   | If(e, s1, s2) -> If(applye e, applys s1, match s2 with None -> None | Some s2 -> Some (applys s2))
   | Do(s, e) -> Do(applys s, applye e)
   | While(e, s) -> While(applye e, applys s)
   | For(eoi, eoc, eoe, s) -> For(
       (match eoi with None -> None
       | Some(Declaration(i, dl),loc) -> Some(Declaration(i, List.map (fun (k,eo) -> k, (match eo with None -> None | Some e -> Some (applye e))) dl), loc)),
       (match eoc with None -> None | Some e -> Some (applye e)),
       (match eoe with None -> None | Some e -> Some (applye e)),
       applys s)
   | With(e, s) -> With(applye e, applys s)
   | Try(s, catch, fin) -> failwith "Try"
   | s -> bases s
   in (rs, loc)
  and applye ((e, loc):expression_t) : expression_t =
   let re = match e with
   | Array(el) -> Array(List.map applye el)
   | New(e, elo) -> New(applye e, match elo with None -> None | Some el -> Some (List.map applye el))
   | Typeof(e) -> Typeof(applye e)
   | Delete(e) -> Delete(applye e)
   | Void(e) -> Void(applye e)
   | Plus(e) -> Plus(applye e)
   | Preincr(e) -> Preincr(applye e)
   | Postincr(e) -> Postincr(applye e)
   | Predecr(e) -> Predecr(applye e)
   | Postdecr(e) -> Postdecr(applye e)
   | Minus(e) -> Minus(applye e)
   | Lnot(e) -> Lnot(applye e)
   | Bnot(e) -> Bnot(applye e)
   | Conditional(e1, e2, e3) -> Conditional(applye e1, applye e2, applye e3)
   | Sequence(el) -> Sequence(List.map applye el)
   | Assign(e1, e2) -> Assign(applye e1, applye e2)
   | Ashassign(e1, e2) -> Ashassign(applye e1, applye e2)
   | Property(e1, e2) -> Property(applye e1, applye e2)
   | Dot(e, i) -> Dot(applye e, i)
   | In(e1, e2) -> In(applye e1, applye e2)
   | Instanceof(e1, e2) -> Instanceof(applye e1, applye e2)
   | Add(e1, e2) -> Add(applye e1, applye e2)
   | Sub(e1, e2) -> Sub(applye e1, applye e2)
   | Multiply(e1, e2) -> Multiply(applye e1, applye e2)
   | Mod(e1, e2) -> Mod(applye e1, applye e2)
   | Divide(e1, e2) -> Divide(applye e1, applye e2)
   | Lsh(e1, e2) -> Lsh(applye e1, applye e2)
   | Rsh(e1, e2) -> Rsh(applye e1, applye e2)
   | Ash(e1, e2) -> Ash(applye e1, applye e2)
   | Lor(e1, e2) -> Lor(applye e1, applye e2)
   | Land(e1, e2) -> Land(applye e1, applye e2)
   | Bor(e1, e2) -> Bor(applye e1, applye e2)
   | Band(e1, e2) -> Band(applye e1, applye e2)
   | Bxor(e1, e2) -> Bxor(applye e1, applye e2)
   | Equal(e1, e2) -> Equal(applye e1, applye e2)
   | Lt(e1, e2) -> Lt(applye e1, applye e2)
   | Gt(e1, e2) -> Gt(applye e1, applye e2)
   | Le(e1, e2) -> Le(applye e1, applye e2)
   | Ge(e1, e2) -> Ge(applye e1, applye e2)
   | Sequal(e1, e2) -> Sequal(applye e1, applye e2)
   | Call(e, el) -> Call(applye e, List.map applye el)
   | e -> basee e
   in (re, loc)
  in List.map applys body

let extract_method ((acc, env, menv):string*env*menv) = function
  | Method(q, (f, args, body)) ->
    let env = match f with None -> env | Some x -> Smap.add x MethodName env in
    let rt = ref (Named "unit", None) in
    let transform body qual =
      (match qual with
      | Returns(rty, x) -> rt := (rty, x); body
      | Modified(f, el) ->
        let (f,args,b) = try
          Smap.find f menv
        with Not_found -> failwith "applied undefined modifier" in
        (match (el, args) with
        | (None, []) -> ast_map (function
            | Expression((Identifier("_"),_)) -> Block(body)
            | s -> s) (fun e->e) b
        | (Some el, vl) when List.length el = List.length vl ->
          let vl = List.map (fun (t,x)->x) vl in
          let substitution = List.combine vl el in
          let b = ast_map (fun x->x) (function
            | Identifier i -> (try
              fst (List.assoc i substitution)
              with Not_found -> Identifier i)
            | e -> e) b in
          let merged = ast_map (function
            | Expression((Identifier("_"),_)) -> Block(body)
            | s -> s) (fun e->e) b in
          merged
        | _ -> failwith "modifier arity mismatch")
      | x -> body) in
     let body = List.fold_left transform body q in
     let carg (t,x) = sprintf "(%s:%s)" x (ty false t) in
     let renv = match !rt with (_, Some x) -> Smap.add x Local env | _ -> env in
     let acc = sprintf "%s\nlet %s %s : GoodEth %s =\n" acc
       (match f with None -> "__default" | Some x -> BatString.uncapitalize x)
       (match args with [] -> "()" | args -> BatString.concat " " (List.map carg args))
       (let rtyp, _ = !rt in ty false rtyp) in
     let (_, loc) = List.hd body in
     let sinit = match f with Some x when x = !contract_name -> !cons_allocs | _ -> "" in
     let content = compile_s 1 env (Block(body),loc) in
     (acc^sinit^content^"\n", env, menv)
  | Event(_, _) -> (acc, env, menv)
  | _ -> failwith "Compiler bug (non-method after filtering)"

(* Extract modifiers *)
let rec extract_modifiers (env, l) = function
  | [] -> (env, l)
  | Modifier((Some f), arg, body) :: t ->
    extract_modifiers (Smap.add f (Some f, arg, body) env, l) t
  | h :: t -> extract_modifiers (env, l @ [h]) t

(* Extract all the contract state and pack it in a record *)
let rec extract_state (vs, s, env, l) = function
  | [] -> (vs, s, env, l)
  | Statevar(typ, x, eo) :: t ->
    (match eo with None -> ()
    | Some e -> cons_allocs := sprintf "%s%sstore.%s := %s;\n" !cons_allocs (pad 1) x (compile_e 1 env e));
    let ps = sprintf "\t%s: %s;\n" (BatString.uncapitalize x) (ty true typ) in
    let vcs = sprintf "contains h s.%s" (BatString.uncapitalize x) in
    let vs = if vs = "" then "  " ^ vcs else vs ^ "\n  /\\ " ^ vcs in
    extract_state (vs, s ^ ps, Smap.add x State env, l) t
  | h :: t -> extract_state (vs, s, env, l @ [h]) t

(* Extract all type declarations in contract *)
let rec extract_types (s, env, l) = function
  | [] -> (s, env, l)
  | Typedef (x,vl) :: t ->
    let vlo = List.fold_left (fun a (t, x) -> a ^ "\t" ^ (BatString.uncapitalize x) ^ ": " ^ (ty false t) ^ ";\n") "" vl in
    let enums = sprintf "type %s = {\n%s}\n\n" (BatString.uncapitalize x) vlo in
    extract_types (s ^ enums, env, l) t
  | Enum(x, vl) :: t ->
    let addenv (e,a) x = (Smap.add x EnumConst env), (a ^ "| " ^ (BatString.capitalize x) ^ "\n") in
    let env, vlo = List.fold_left addenv (env, "") vl in
    let enums = sprintf "type %s =\n%s\n\n" (BatString.uncapitalize x) vlo in
    extract_types (s ^ enums, env, l) t
  | h :: t -> extract_types (s, env, l @ [h]) t

(* Compile a contract *)
let compile_contract = function
  | Contract (x, decl), _ ->
    contract_name := x;
    cons_allocs := "";
    let env : env = Smap.empty in
    let x = BatString.capitalize x in
    let tdecs, env, others = extract_types ("", env, []) decl in
    w "module %s\n\nopen FStar.Heap\nopen FStar.ST\nopen Solidity\n\n%s\n" x tdecs;
    let sval, sdec, env, others = extract_state ("", "", env, []) others in
    w "type state = {\n%s}\n\nlet validStore h s = (\n%s)\n\n" sdec sval;
    w "assume val getStorage: unit -> ST storage\n";
    w "  (requires (fun h -> true))\n";
    w "  (ensures (fun h x h' -> h=h' /\\ validStore h' x))\n\n";
    w "let store = getStorage()\n";
    w "let msg = getMessage()\n";
    w "let block = getBlock()\n\n";
    let menv : menv = Smap.empty in
    let (menv, methods) = extract_modifiers (menv, others) others in
    let smethods, env, menv = List.fold_left extract_method ("", env, menv) methods in
    w "%s\n" smethods

let compile (x:t) =
  List.iter compile_contract x


