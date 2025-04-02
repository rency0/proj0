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
  | TmIf of term * term * term
  | TmPair of term * term
  | TmFst of term
  | TmSnd of term
  | TmVar of string
  | TmLam of string * tp * term
  | TmApp of term * term


type context = (name * tp) list
type constr = (tp * tp) list

exception UnificationError


let rec generateconstraints context tm = 
  | TmTrue -> 
  | TmFalse -> 
  | TmApp(e1,e2)-> let t1,c1= generateconstraints context e1 in
                    let t2,c2= generateconstraints context e2 in  

  | TpArr(t1,t2)-> 
  | TmIf(cond,t1)-> 

let rec unify constraints= 
match constraints with 
|  [] -> [] (*If constraint set is empty*)
| (s,t):: C' -> if s=t then unify C' 
                else match (s,t) with
                | (TpVar x,t) when not (freevarscheck(x t))-> (x,t) ::unify (subst(x,t)  C') (*Add the constraint*)
                | (t,TpVar x) when not (freevarscheck(x t))-> (t,x) ::unify (subst(t,x)  C') (*Symmetric*)
                | (TpArr(s1,s2), TpArr(t1,t2)) -> unify((s1,t1)::(s2,t2)::C')
                | (*Case for user defined TO DO*)
                | _ -> failwith UnificationError


  let rec freevarscheck x t =
  match t with 
  | TpVar y -> x=y
  | TpArr(t1,t2) -> freevarscheck x t1 && freevarscheck x t2
    (* |Case for user defined TO DO*)
  |  _ -> false

  let rec subst  =

