type type_name = string
type var_name = string 

type tp = 
  | TpBool | TpNat | TpUnit
  | TpArr of tp * tp    (* T1 -> T2 *)
  | TpPair of tp * tp   (* (T1, T2) *)
  | TpVar of type_name  (* type "X" *)
  | TpDef of type_name * tp  (* define "X" = type *)


type term = 
  | TmUnit
  | TmVar of var_name
  | TmLet of var_name * term * term (* let x = t1 in t2 *)
  (* Bools *)
  | TmTrue 
  | TmFalse 
  | TmIsZero of term
  (* Nats *)
  | TmZero 
  | TmSucc of term 
  | TmPred of term
  (* L-calc *)
  | TmLam of (var_name * tp) * term (*THINK: maybe don't need type in λ (x:T) . t*)
  | TmApp of term * term
  (* Pairs *)
  | TmPair of term * term 
  | TmFst of term 
  | TmSnd of term
  (* If then else *)
  | TmIf of term * term * term


type context = (name * tp) list
type constr = (tp * tp) list

exception UnificationError

let rec generateconstraints context tm =
  match tm with
  | TmVar x -> (try [(List.assoc x context, TpVar x)] with Not_found -> []) (*not sure*)
  | TmUnit| TmTrue | TmFalse | TmZero -> [] 
  | TmSucc n -> let c = generateconstraints context n in 
                (TpNat,TpVar x)
  | TmPred ->
  | TmIsZero ->
  | TmLet ->
  | TmLam(x,typ,t1) -> generateconstraints ((x,typ)::context) t1 (*Adds x:typ to context*)
  | TmFst t1 -> generateconstraints context t1
  | TmSnd t1 -> generateconstraints context t1
  | TmPair(t1,t2) -> let c1 = generateconstraints context t1 in
                     let c2 = generateconstraints context t2 in
                     (c1@c2) (*also not sure*)
  | TmApp(t1,t2)->let c1 = generateconstraints context t1 in 
                  let c2 = generateconstraints context t2 in
                  let t1= List.assoc t1 context in
                  let t2 = List.assoc t2 context in 
                  ((t1,TpArr(t2, TpVar "x"))::(c1@c2))
    (*TmIF : ensures condition is bool*)
  | TmIf(cond,t1,t2)-> let c1 = generateconstraints context cond in
                       let c2 = generateconstraints context t1 in
                       let c3 = generateconstraints context t2 in
                       ((List.assoc cond, TpBool):: (List.assoc t1 context, List.assoc t2 i=context)::(c1@c2@c3))



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
  | TpArr(t1,t2) -> freevarscheck x t1 || freevarscheck x t2
  | TmPair(t1,t2) -> freevarscheck x t1 || freevarscheck x t2
    (* |Case for user defined TO DO*)
  |  _ -> false

  let rec subst  =

