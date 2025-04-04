
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
  | TmLam of (var_name * tp) * term 
  | TmApp of term * term
  | TmFix of (var_name * tp)  * term * term 
  (* Pairs *)
  | TmPair of term * term 
  | TmFst of term 
  | TmSnd of term
  (* If then else *)
  | TmIf of term * term * term 
  | TmTypedef of (type_name * tp) * term (* define type X = T in t1 *)
  


type context = (var_name * tp) list
type sigma  = (type_name * tp) list
type constr = (tp * tp) list 

exception UnificationError of string


(* Pretty printing functions *)
let rec tp_to_str (t:tp) : string = match t with 
  | TpBool -> "Bool"
  | TpNat -> "Nat"
  | TpUnit -> "Unit"
  | TpArr (t1, t2) -> "(" ^ (tp_to_str t1) ^ " -> " ^ (tp_to_str t2) ^ ")"
  | TpPair (t1, t2) -> "(" ^ (tp_to_str t1) ^ ", " ^ (tp_to_str t2) ^ ")"
  | TpVar x -> x
  | TpDef (x, t1) ->  "(" ^ x ^ " := " ^ (tp_to_str t1) ^ ")" 
let rec term_to_str (t:term) : string = match t with 
  | TmUnit  -> "unit"
  | TmTrue  -> "true"
  | TmFalse -> "false"
  | TmZero  -> "zero"
  | TmVar x -> x
  | TmLet (x, t1, t2) -> "let " ^ x ^ " = " ^ (term_to_str t1) ^ " in " ^ (term_to_str t2)
  | TmIsZero t1 -> "iszero (" ^ (term_to_str t1) ^ ")"
  | TmSucc t1 -> "succ (" ^ (term_to_str t1) ^ ")"
  | TmPred t1 -> "pred (" ^ (term_to_str t1) ^ ")"
  | TmLam ((x, tp), t) -> "λ" ^ x ^ ":" ^ (tp_to_str tp) ^ "." ^ (term_to_str t)
  | TmApp (t1, t2) -> "(" ^ (term_to_str t1) ^ ") (" ^ (term_to_str t2) ^ ")"
  | TmPair (t1, t2) -> "<" ^ (term_to_str t1) ^ ", " ^ (term_to_str t2) ^ ">"
  | TmFst t1 -> "fst " ^ (term_to_str t1)
  | TmSnd t1 -> "snd " ^ (term_to_str t1)
  | TmIf (t1, t2, t3) -> "if (" ^ (term_to_str t1) ^ ") then {" ^ (term_to_str t2) ^ "} else {" ^ (term_to_str t3) ^ "}"
  | TmFix ((x, tp) , t1, t2) -> "let rec " ^ x ^ ":" ^ (tp_to_str tp) ^ " = " ^ (term_to_str t1) ^ " in " ^ (term_to_str t2)
  | TmTypedef ((x, tp), t) -> "let type " ^ x ^ " := " ^ (tp_to_str tp) ^ " in " ^ (term_to_str t) 
let print_constraints (constraints:constr) : unit = 
  List.iter (fun (s, t) -> Printf.printf "%s = %s\n" (tp_to_str s) (tp_to_str t)) constraints
let print_sigma (sigma:sigma) : unit =
  List.iter (fun (x, t) -> Printf.printf "%s = %s\n" x (tp_to_str t)) sigma
(* ------------------------- *)

(* creation of constraints based off of term *)
let remove_binding (x : var_name) (ctx : context) : context =
  List.filter (fun (y, _) -> y <> x) ctx

let rec generateconstraints (ctx : context) (tm : term) : tp * constr =
  match tm with
  | TmVar x ->(match List.assoc_opt x ctx with
              | Some t -> (t, [])
              | None ->  raise (UnificationError ("Variable "^ x ^" not found")))
  | TmUnit ->  (TpUnit, [])
  | TmTrue ->  (TpBool, [])
  | TmFalse -> (TpBool, [])
  | TmZero ->  (TpNat, [])
  | TmSucc t1 -> let (typ, c) = generateconstraints ctx t1 in (TpNat, c @ [(typ, TpNat)]) (* enforce that t1: TpNat *)
  | TmPred t1 -> let (typ, c) = generateconstraints ctx t1 in (TpNat, c @ [(typ, TpNat)])
  | TmIsZero t1 -> let (typ, c) = generateconstraints ctx t1 in(TpBool, c @ [(typ, TpNat)]) (* enforce t1:TpNat and the result is a bool*)
  | TmLam((x, typ), t1) -> let (t1_type, c) = generateconstraints ((x, typ) :: ctx)  t1 in (TpArr(typ, t1_type), c) (* THINK : do we need to remove x from the og ctx?*)
  | TmTypedef ((typ_name, typ) , t) ->
    let (t_typ ,c) = generateconstraints ctx t in 
    ( t_typ , ((TpVar typ_name, typ)::c )) 
  | TmApp(t1, t2) -> let (t1_type, c1) = generateconstraints ctx t1 in
                      let (t2_type, c2) = generateconstraints ctx t2 in
                      let f = TpVar ("'" ^ term_to_str(t1) ^ "'_x_app") in  
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
                  let a = TpVar ("'" ^ term_to_str(t1) ^ "_a_fst") and b = TpVar ("'" ^ term_to_str(t1) ^ "'_b_fst") in
                  let c_fst = [(typ, TpPair(a, b))] in  (a, c @ c_fst)
  | TmSnd t1 -> let (typ, c) = generateconstraints ctx t1 in
                let a = TpVar  ("'" ^ term_to_str(t1) ^ "'_a_snd") and b = TpVar  ("'" ^ term_to_str(t1) ^ "'_b_snd") in
                let c_snd = [(typ, TpPair(a, b))] in (b, c @ c_snd)
  | TmIf(cond, t1, t2) -> let (cond_type, c_cond) = generateconstraints ctx cond in
                          let (t1_type, c1) = generateconstraints ctx t1 in
                          let (t2_type, c2) = generateconstraints ctx t2 in
                          (* Condition must be boolean and branches must have the same type *)
                          let c_if = [(cond_type, TpBool); (t1_type, t2_type)] in
                          (t1_type, c_cond @ c1 @ c2 @ c_if)                          
  | TmFix((x, typ), t1, t2) -> 
     let ctx' = (x, typ) :: (remove_binding x ctx) in
     let (t1_type, c1) = generateconstraints ctx' t1 in
     let c_fix = [(t1_type, typ)] in
     let (t2_type, c2) = generateconstraints ctx' t2 in
     (t2_type, c1 @ c_fix @ c2)



  (* construction of type substitutions satisfying the constraints *)
let rec unify (constraints:constr) : sigma =
  match constraints with
  | [] -> []
  | (s, t) :: rest -> 
    if s = t then unify rest
    else  (match (s, t) with 
        | (TpArr (s1, s2), TpArr (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpPair (s1, s2), TpPair (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpDef (x, s), t) -> unify ((TpVar x, s) :: (TpVar x , t) :: rest )
        | (t, TpDef (x, s)) -> unify ((TpVar x, s) :: (TpVar x , t) :: rest )
        | (TpVar x, t) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (t, TpVar x) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | ( _ , _ ) -> raise (UnificationError ("Unification failed: " ^ (tp_to_str s) ^ " = " ^ (tp_to_str t)) )
      )
  (* X ∈ FV(T) *)
and occurs (x:type_name) (t:tp) : bool =
  match t with
  | TpVar y -> x = y
  | TpArr (t1, t2) -> occurs x t1 || occurs x t2
  | TpPair (t1, t2) -> occurs x t1 || occurs x t2
  | TpDef (y, t1) -> x = y || occurs x t1
  | _ -> false

  (* [X/T] C *)
and subst ((x:type_name), (t:tp)) (constraints:constr) : constr =
  List.map (fun (s, u) -> (replace x t s, replace x t u)) constraints

  (* [X/T] T' *) (* REF: tb section 22.1.1 *)
  and replace (x:type_name) (t:tp) (t':tp) : tp  =
  match t' with
  | TpVar y -> if y = x then t else t' 
  | TpDef (y, t1) -> if y = x then t else TpDef (y, replace x t t1) (* THINK (name, List.map (replace x t) t1)*)
  | TpArr (t1, t2) -> TpArr (replace x t t1, replace x t t2)
  | TpPair (t1, t2) -> TpPair (replace x t t1, replace x t t2)
  | _ -> t'




let check_type (program:term) (intended_type:tp) : unit = 
  let (inferred_type, constraints) = generateconstraints [] program in
  let inferred_subs = unify constraints in
  let result_type = List.fold_right (fun (x, t_sub) acc -> replace x t_sub acc) inferred_subs inferred_type in
  if ((tp_to_str result_type) = (tp_to_str intended_type)) then 
    print_endline ("Type check successful: " ^ (tp_to_str intended_type) )
  else
    print_endline ("Type check failed: expected " ^ (tp_to_str intended_type) ^ " but got " ^ (tp_to_str result_type))

(* Testing *)



(* ---- succsesful programs ----  *)


