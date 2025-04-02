let () = print_endline "Hello, World!"

type type_name = string
type var_name = string 

type tp = 
  | TpBool | TpNat | TpUnit
  | TpArr of tp * tp    (* T1 -> T2 *)
  | TpPair of tp * tp   (* (T1, T2) *)
  | TpVar of type_name  (* type alpha *)
  | TpDef of name * tp  (* define "X" = type *)
  | TpRec of tp         (* maybe ? *)


type term = 
  | TmTrue | TmFalse 
  | TmUnit
  | 
  | TmIf of term * term * term
  | TmPair of term * term
  | TmFst of term
  | TmSnd of term
  | TmVar of string
  | TmLam of string * tp * term
  | TmApp of term * term


type context = (name * tp) list



let tp1 = TpArr( TpArr(TpInt, TpInt), TpVar("x"))
let tp2 = TpDef( "my", tp1) 

