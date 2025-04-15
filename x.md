```ocaml 


(* AST = Abstract Syntax Tree *)
type scheme = Forall of (type_name list) * tp 

type const_def = 
| ConstructorDef of name * tp list (* | <name> of <tp list> *)
and top_level =
| Defintion of name * tp * term (* let <name> : <tp> = <term> *)
| TypeDef of name * const_def list (* type <name> = <const_def list> *)
and tp = ...
| DefinedType of name

type term = ...
| Constructor of name * term list (* <name> (<term list>) *)

type program = top_level list

(**
type orig = Orig of int
type both = One of float | TheOther of double

let x : orig = Orig 5
*)

(* type_check
["orig", ["Orig", TpInt]; "both", ["One", TpFloat; "TheOther", TpDouble]]
[]
(Constructor ("Orig", [TmInt 5]))
(DefinedType "orig") *)

(* Type Checking / Evaluation / Unification *)
type context = (var_name * scheme) list
type sigma = (type_name * tp) list
type signature = (name * tp * const_def list) list
type constr = (tp * tp) list

let type_check : signature -> context -> term -> tp ->
```