open Printf

type loc = Lexing.position * Lexing.position
type 'a located = 'a * loc

(* Type of Javascript program *)
type t = source_t located list 

and source_t =
	| Contract of identifier_t * (decl_t list)

and type_t =
        | Named of identifier_t
        | Array of type_t
        | Mapping of identifier_t * type_t

and fqual =
        | Internal
        | External
        | Private
        | Public
        | Constant
        | Returns of (type_t * identifier_t option)
        | Modified of identifier_t * (expression_t list) option

and decl_t =
        | Statevar of type_t * identifier_t * (expression_t option)
        | Typedef of identifier_t * (type_t * identifier_t) list
        | Method of fqual list * function_t
        | Modifier of function_t
        | Enum of identifier_t * (identifier_t list)
        | Event of identifier_t * (type_t * identifier_t) list

and statement_t = stmt_t located

and stmt_t =
	| Empty
	| Debugger
	| Return of expression_t option
	| Throw
	| Continue of identifier_t option
	| Break of identifier_t option
	| Try of statement_t * (identifier_t * statement_t) option * statement_t option 
	| Block of statement_t list
	| Label of identifier_t * statement_t
	| Expression of expression_t
	| Declaration of identifier_t * (identifier_t * expression_t option) list
	| If of expression_t * statement_t * statement_t option
	| Do of statement_t * expression_t
	| While of expression_t * statement_t
	| For of forinit_t option * expression_t option * expression_t option * statement_t
	| With of expression_t * statement_t
	| Switch of expression_t * statement_t list option * (expression_t * statement_t list) list

and forinit_t = finit_t located 

and finit_t =
	| Declaration of identifier_t * (identifier_t * expression_t option) list

and identifier_t = string

and function_t = identifier_t option * (type_t * identifier_t) list * fbody_t

and fbody_t = statement_t list

and object_prop_t = (string * expression_t) located

and expression_t = expr_t located

and expr_t =
	| This
	| Null
	| Undefined
	| Elision
	| Bool of bool
	| Byte of int
	| Number of float
	| String of string
	| Regexp of (string * string)
	| Identifier of identifier_t
	| Array of expression_t list
	| Object of object_prop_t list
	| New of expression_t * (expression_t list) option
	| Typeof of expression_t
	| Delete of expression_t
	| Void of expression_t
	| Function of function_t
	| Plus of expression_t
	| Preincr of expression_t
	| Postincr of expression_t
	| Predecr of expression_t
	| Postdecr of expression_t
	| Minus of expression_t
	| Lnot of expression_t
	| Bnot of expression_t
	| Conditional of (expression_t * expression_t * expression_t)
	| Sequence of expression_t list
	| Assign of (expression_t * expression_t)
	| Ashassign of (expression_t * expression_t)
	| Property of (expression_t * expression_t)
	| Dot of (expression_t * identifier_t)
	| In of (expression_t * expression_t)
	| Instanceof of (expression_t * expression_t)
	| Add of (expression_t * expression_t)
	| Sub of (expression_t * expression_t)
	| Multiply of (expression_t * expression_t)
	| Mod of (expression_t * expression_t)
	| Divide of (expression_t * expression_t)
	| Lsh of (expression_t * expression_t)
	| Rsh of (expression_t * expression_t)
	| Ash of (expression_t * expression_t)
	| Lor of (expression_t * expression_t)
	| Land of (expression_t * expression_t)
	| Bor of (expression_t * expression_t)
	| Band of (expression_t * expression_t)
	| Bxor of (expression_t * expression_t)
	| Equal of (expression_t * expression_t)
	| Lt of (expression_t * expression_t)
	| Gt of (expression_t * expression_t)
	| Le of (expression_t * expression_t)
	| Ge of (expression_t * expression_t)
	| Sequal of (expression_t * expression_t)
	| Call of expression_t * expression_t list
