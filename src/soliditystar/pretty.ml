open Ast
open Printf
open Globals

let pad = (fun n->String.make (!pad_len*n) ' ')

let rec pretty_print d (program:Ast.t) = 
  let print acc = function
    | (Contract(i, s),loc) ->
        let decl_printer acc x = acc ^ (pretty_print_decl x) in
        let body = List.fold_left decl_printer "" s in
        sprintf "%s\ncontract %s {\n%s\n}\n" acc i body
  in List.fold_left print "" program

and pretty_print_decl (d:decl_t) =
  match d with
  | Statevar(t, x, eo) ->
    (pad 1) ^ (pretty_print_tvar (t,x))
    ^ (match eo with None -> "" | Some e -> " = " ^ (pretty_print_exp 0 e)) ^ ";\n"
  | Event(x, el) -> sprintf "%sevent %s(%s);\n" (pad 1) x (pretty_print_tvar_list el)
  | Enum(x, vl) -> sprintf "%senum %s {%s}\n" (pad 1) x (BatString.concat ", " vl)
  | Typedef(x, el) ->
    let els = List.map pretty_print_tvar el in
    let els = List.map (fun s -> (pad 2)^s) els in
    let els = List.fold_left (fun a s -> a^s^";\n") "" els in
    sprintf "%sstruct %s {\n%s%s}\n" (pad 1) x els (pad 1)
  | Method(q, f) -> pretty_print_function (Some q) f
  | Modifier(x, a, b) -> pretty_print_function None (x, a, b)
  | _ -> ""

and pretty_print_statement ?nopad:(np=false) d ((p,loc):statement_t) =
  let pl d ((s,loc):statement_t) = match s with Block(_) -> d | _ -> d+1 in 
  let f = function
  | Empty -> ";"
  | Debugger -> "debugger;"
  | Return(e) -> "return"^(match e with None->"" | Some v->" "^(pretty_print_exp d v))^";"
  | Throw -> "throw;"
  | Break(i) -> "break"^(match i with None->"" | Some v->" "^v)^";"
  | Continue(i) -> "continue"^(match i with None->"" | Some v->" "^(recode_utf8 v))^";"
  | Block(l) -> "{\n"^(pretty_print_statements (d+1) l)^(pad d)^"}";
  | Label(l, s) -> (recode_utf8 l)^":\n"^(pretty_print_statement (d+1) s)
  | Expression(e) -> (pretty_print_exp d e)^";"
  | If(c,t,f) -> "if("^(pretty_print_exp d c)^")\n"^(pretty_print_statement (pl d t) t)
      ^(match f with None -> "" | Some s->(pad d)^"else"
      ^(match s with (If(_),loc) -> " "^(pretty_print_statement ~nopad:true d s)
        | _ -> "\n"^(pretty_print_statement (pl d s) s)))
  | Do(s,e) -> "do\n"^(pretty_print_statement (pl d s) s)^(pad d)^"while("^(pretty_print_exp d e)^");\n"
  | While(e,s) -> "while("^(pretty_print_exp d e)^")\n"^(pretty_print_statement (pl d s) s)
  | For(i,c,l,s) -> "for("^(match i with None->" " | Some (e,_) ->
      (match e with (* Expression(f) -> pretty_print_exp d ~inless:true f  *)
        | Declaration(t, l) -> (t) ^ " " ^ List.fold_right (fun (i,v) b ->(recode_utf8 i) 
        ^(match v with None -> "" | Some v -> " = "^(pretty_print_exp d ~commaless:true v))
        ^(if b="" then b else ", "^b)) l ""))^"; "
      ^(match c with None->"" | Some e->pretty_print_exp d e)^"; "
      ^(match l with None->"" | Some e->pretty_print_exp d e)^")\n"
      ^(pretty_print_statement (pl d s) s)
  | With(e,s) -> "with("^(pretty_print_exp d e)^")\n"^(pretty_print_statement (pl d s) s)
  | Switch(e,def,cases) -> "switch("^(pretty_print_exp d e)^")\n"^(pad d)^"{\n"
      ^(List.fold_left (fun a (e,l)->a^(pad (d+1))^"case "^(pretty_print_exp d e)^":\n"^(pretty_print_statements (d+2) l)) "" cases)
      ^(match def with None->"" | Some l->(pad (d+1))^"default:\n"^(pretty_print_statements (d+2) l))^(pad d)^"}\n"
  | Try(b,c,f) -> "try\n"^(pretty_print_statement (pl d b) b)
      ^(match c with Some (i,c)->(pad d)^"catch("^i^")\n"^(pretty_print_statement (pl d c) c) | None->"")
      ^(match f with Some f->(pad d)^"finally\n"^(pretty_print_statement (pl d f) f) | None->"")
  | Declaration(t, l) -> (t) ^ " " ^ (List.fold_right
      (fun (i,v) b -> (recode_utf8 i)^(match v with None->""
      | Some v->" = "^(pretty_print_exp (d+1) ~commaless:true v))^(if b="" then b else ",\n"^(pad (d+1))^b)) l "")^";"
  in (if np then "" else pad d)^(f p)^"\n"

and pretty_print_statements d l = List.fold_left (fun a b->a^(pretty_print_statement d b)) "" l

and pt s b = if b then "("^s^")" else s

and pretty_print_exp ?commaless:(cl=false) ?inless:(il=false) d =
  let rec ppe d (input, loc) = match input with
  | This -> ("this", 0)
  | Null -> ("null", 0)
  | Undefined -> ("undefined", 0)
  | Elision -> ("undefined", 0)
  | Bool(b) -> ((if b then "true" else "false"), 0) 
  | Number(n) -> (cutdot (sprintf "%F" n), 0)
  | String(s) -> ("\""^(recode_utf8 s)^"\"", 0)
  | Regexp(r,f) -> ("/"^(recode_utf8 ~regexp:true r)^"/"^f, 0)
  | Identifier(id) -> (recode_utf8 id, 0)
  | Array(l) -> ((if List.length l > 0 then "[" ^ (pretty_print_elist (d+1) l) ^ "]" else "[]"), 0)
  | Object(l) -> ((if List.length l > 0 then "{\n"^(pretty_print_object (d+1) l)^(pad d)^"}" else "{}"), 0)
  | Dot(e,i) -> let (s,p)=ppe d e in ((pt s (p>1))^"."^(recode_utf8 i), 1)
  | Property(e,f) -> let (s,p)=ppe d e in ((pt s (p>1))^"["^(pretty_print_exp d f)^"]",1)
  | Call(f, l) -> let (s,p) = ppe d f in ((pt s (p>1))^"("^(pretty_print_elist d l)^")",1)
  | New(e, f) -> let (s,p)=ppe d e in ("new "^(pt s (p>2))
      ^(match f with Some l->"("^(pretty_print_elist d l)^")" |None->""), 2)
  | Preincr(e) -> let (s,p)=ppe d e in ("++"^(pt s (p>3)), 3)
  | Predecr(e) -> let (s,p)=ppe d e in ("--"^(pt s (p>3)), 3)
  | Postincr(e) -> let (s,p)=ppe d e in ((pt s (p>3))^"++", 3)
  | Postdecr(e) -> let (s,p)=ppe d e in ((pt s (p>3))^"--", 3)
  | Plus(e) -> let (s,p)=ppe d e in ("+"^(pt s (p>3)), 3)
  | Minus(e) -> let (s,p)=ppe d e in ("-"^(pt s (p>3)), 3)
  | Bnot(e) -> let (s,p)=ppe d e in ("~"^(pt s (p>3)), 3)
  | Lnot(e) -> let (s,p)=ppe d e in ("!"^(pt s (p>3)), 3)
  | Typeof(e) -> let (s,p)=ppe d e in ("typeof "^(pt s (p>3)), 3)
  | Delete(e) -> let (s,p)=ppe d e in ("delete "^(pt s (p>3)), 3)
  | Void(e) -> let (s,p)=ppe d e in ("void "^(pt s (p>3)), 3)
  | Mod(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>6))^" % "^ (pt s2 (p2>3)), 4)
  | Divide(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>6))^" / "^ (pt s2 (p2>4)), 5)
  | Multiply(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>6))^" * "^ (pt s2 (p2>6)), 6)
  | Add(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>7))^" + "^ (pt s2 (p2>7)), 7)
  | Sub(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>7))^" - "^ (pt s2 (p2>7)), 7)
  | Lsh(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>8))^" << "^ (pt s2 (p2>7)), 8)
  | Rsh(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>8))^" >> "^ (pt s2 (p2>7)), 8)
  | Ash(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>8))^" >>> "^ (pt s2 (p2>7)), 8)
  | Lt(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>9))^" < "^ (pt s2 (p2>8)), 9)
  | Gt(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>9))^" > "^ (pt s2 (p2>8)), 9)
  | Le(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>9))^" <= "^ (pt s2 (p2>8)), 9)
  | Ge(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>9))^" >= "^ (pt s2 (p2>8)), 9)
  | In(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in (pt ((pt s1 (p1>9))^" in "^ (pt s2 (p2>8))) il, 9)
  | Instanceof(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>9))^" instanceof "^ (pt s2 (p2>8)), 9)
  | Equal(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>10))^" == "^ (pt s2 (p2>9)), 10)
  | Sequal(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>10))^" === "^ (pt s2 (p2>9)), 10)
  | Band(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>11))^" & "^ (pt s2 (p2>10)), 11)
  | Bxor(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>12))^" ^ "^ (pt s2 (p2>11)), 12)
  | Bor(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>13))^" | "^ (pt s2 (p2>12)), 13)
  | Land(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>14))^" && "^ (pt s2 (p2>13)), 14)
  | Lor(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>15))^" || "^ (pt s2 (p2>14)), 15)
  | Conditional(c,e,f) -> let (s1,p1)=ppe d c and (s2,p2)=ppe d e and (s3,p3)=ppe d f in
    ((pt s1 (p1>16))^" ? "^ (pt s2 (p2>16)) ^ " : " ^ (pt s3 (p3>16)), 16)
  | Assign(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>16))^" = "^ (pt s2 (p2>17)), 17)
	| Ashassign(e,f) -> let (s1,p1)=ppe d e and (s2,p2)=ppe d f in ((pt s1 (p1>16))^" >>>= "^ (pt s2 (p2>17)), 17)
  | Sequence(e) -> (pt (pretty_print_elist d e) cl, 18)
  | _ -> ("<unknown expression>", 0)
  in fun e -> fst (ppe d e)

and pretty_print_type = function
  | Named x -> x
  | Array(t) -> sprintf "%s[]" (pretty_print_type t)
  | Mapping(x, t) -> sprintf "mapping (%s => %s)" x (pretty_print_type t)

and pretty_print_tvar (t,x) =
  sprintf "%s %s" (pretty_print_type t) x

and pretty_print_tvar_list = function
  | [] -> ""
  | [h] -> pretty_print_tvar h
  | h :: t -> sprintf "%s, %s" (pretty_print_tvar_list [h]) (pretty_print_tvar_list t)

and pretty_print_elist d = function
  | [h] -> (pretty_print_exp d ~commaless:true h)
  | h::t  -> (pretty_print_exp d ~commaless:true h)^", "^(pretty_print_elist d t)
  | [] -> ""

and pretty_print_fquals fq =
  let aux = function
    | Internal -> "internal"
    | External -> "external"
    | Private -> "private"
    | Public -> "public"
    | Constant -> "constant"
    | Returns (t,x) ->
      sprintf "returns (%s%s)" (pretty_print_type t) (match x with None->"" | Some x -> " "^(recode_utf8 x))
    | Modified (t, elo) ->
      sprintf "%s%s" t (match elo with None -> ""
        | Some el -> "("^(pretty_print_elist 2 el)^")")
  in
  let fq = List.map (fun x->" "^(aux x)) fq in
  List.fold_left (fun acc x -> acc^x) "" fq

and pretty_print_fbody d b =
  let aux acc x = acc ^ (pretty_print_statement (d+1) x) in
  List.fold_left aux "" b

and pretty_print_function (q : fqual list option) ((n,args,b) : function_t) = 
  "\n" ^ (pad 1) ^ (match q with None -> "modifier " | Some _ -> "function ")
  ^(match n with Some(i)->(recode_utf8 i) | None->"")
  ^"("^(pretty_print_tvar_list args)^")"
  ^(match q with None -> "" | Some q -> pretty_print_fquals q)
  ^" {\n"^(pretty_print_fbody 1 b)
  ^(pad 1)^"}\n"

and pretty_print_object d = function
  | ((p,v),loc)::t ->
    let p = "\""^(recode_utf8 p)^"\": "^(pretty_print_exp d ~commaless:true v) in
    (pad d) ^ p ^ (if List.length t>0 then "," else "") ^ "\n"
    ^ pretty_print_object d t
  | [] -> ""


