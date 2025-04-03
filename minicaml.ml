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


type context = (var_name * tp) list
type constr = (tp * tp) list

exception UnificationError

let remove_binding (x : var_name) (ctx : context) : context =
  List.filter (fun (y, _) -> y <> x) ctx

let rec generateconstraints (ctx : context) (tm : term) : tp * constr =
  match tm with
  | TmVar x ->(match List.assoc_opt x ctx with
              | Some t -> (t, [])
              | None -> failwith ("Variable "^ x ^" not found"))
  | TmUnit ->  (TpUnit, [(TpUnit, TpUnit)])
  | TmTrue ->  (TpBool, [(TpBool, TpBool)])
  | TmFalse -> (TpBool, [(TpBool, TpBool)])
  | TmZero ->  (TpNat, [(TpNat, TpNat)])
  | TmSucc t1 -> let (typ, c) = generateconstraints ctx t1 in (TpNat, c @ [(typ, TpNat)]) (* enforce that t1: TpNat *)
  | TmPred t1 -> let (typ, c) = generateconstraints ctx t1 in (TpNat, c @ [(typ, TpNat)])
  | TmIsZero t1 -> let (typ, c) = generateconstraints ctx t1 in(TpBool, c @ [(typ, TpNat)]) (* enforce t1:TpNat and the result is a bool*)
  | TmLam((x, typ), t1) -> let (t1_type, c) = generateconstraints ((x, typ) :: ctx)  t1 in (TpArr(typ, t1_type), c)
  | TmApp(t1, t2) -> let (t1_type, c1) = generateconstraints ctx t1 in
                     let (t2_type, c2) = generateconstraints ctx t2 in
                     let f = TpVar "x_app" in  
                     let c_app = [(t1_type, TpArr(t2_type, f))] in (f, c1 @ c2 @ c_app)
  | TmLet(x, t1, t2) -> let (t1_type, c1) = generateconstraints ctx t1 in
        let f= TpVar x in  
        let ctx' = (x, f) :: (remove_binding x ctx) in
        let (t2_type, c2) = generateconstraints ctx' t2 in
        let c_let = [(f, t1_type)] in
        (t2_type, c1 @ c_let @ c2)
  | TmPair(t1, t2) -> let (ty1, c1) = generateconstraints ctx t1 in 
                      let (ty2, c2) = generateconstraints ctx t2 in (TpPair(ty1, ty2), c1 @ c2)
  | TmFst t1 ->  let (typ, c) = generateconstraints ctx t1 in
                 let a = TpVar "a_fst" and b = TpVar "b_fst" in
                 let c_fst = [(typ, TpPair(a, b))] in  (a, c @ c_fst)
  | TmSnd t1 -> let (typ, c) = generateconstraints ctx t1 in
                let a = TpVar "a_snd" and b = TpVar "b_snd" in
                let c_snd = [(typ, TpPair(a, b))] in (b, c @ c_snd)
  | TmIf(cond, t1, t2) -> let (cond_type, c_cond) = generateconstraints ctx cond in
                          let (t1_type, c1) = generateconstraints ctx t1 in
                          let (t2_type, c2) = generateconstraints ctx t2 in
                          (* Condition must be boolean and branches must have the same type *)
                          let c_if = [(cond_type, TpBool); (t1_type, t2_type)] in
                          (t1_type, c_cond @ c1 @ c2 @ c_if)



let rec unify constraints= 
match constraints with 
|  [] -> [] (*If constraint set is empty*)
| (s,t):: c' -> if s=t then unify c' 
                else match (s,t) with
                | (TpVar x,t) when not (freevarscheck x t)-> (x,t) ::unify (subst(x,t)  c') (*Add the constraint*)
                | (t,TpVar x) when not (freevarscheck x t)-> (x,t) ::unify (subst(x,t)  c') (*Symmetric*)
                | (TpArr(s1,s2), TpArr(t1,t2)) -> unify((s1,t1)::(s2,t2)::c')
                 (*Case for user defined TO DO*)
                | _ -> raise UnificationError


  and freevarscheck x t =
  match t with 
  | TpVar y -> x=y
  | TpArr(t1,t2) -> freevarscheck x t1 || freevarscheck x t2
  | TpPair(t1,t2) -> freevarscheck x t1 || freevarscheck x t2
    (* |Case for user defined TO DO*)
  |  _ -> false

  and subst ((x:type_name), (t:tp)) (constraints:constr) : constr =
    List.map (fun (s, u) -> (replace x t s, replace x t u)) constraints
  
    (* [X/T] T' *) (* REF: tb section 22.1.1 *)
    and replace (x:type_name) (t:tp) (t':tp) : tp  =
    match t' with
    | TpVar y -> if y = x then t else t'  (* ?? *)
    | TpDef (y, t1) -> if y = x then t else TpDef (y, replace x t t1) (* (name, List.map (replace x t) t1)*)
    | TpArr (t1, t2) -> TpArr (replace x t t1, replace x t t2)
    | TpPair (t1, t2) -> TpPair (replace x t t1, replace x t t2)
    | _ -> t'
  