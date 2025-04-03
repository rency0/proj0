
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
type sigma  = (type_name * tp) list
type constr = (tp * tp) list 

(* construction of type substitutions satisfying the constraints *)
let rec unify (constraints:constr) : sigma =
  match constraints with
  | [] -> []
  | (s, t) :: rest ->
      if s = t then unify rest
      else match (s, t) with
        | (TpArr (s1, s2), TpArr (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpVar x, t) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (t, TpVar x) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (TpPair (s1, s2), TpPair (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        (*TODO: *)
        | _ -> failwith "Unification failed"

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
  | TpVar y -> if y = x then t else t'  (* ?? *)
  | TpDef (y, t1) -> if y = x then t else TpDef (y, replace x t t1) (* (name, List.map (replace x t) t1)*)
  | TpArr (t1, t2) -> TpArr (replace x t t1, replace x t t2)
  | TpPair (t1, t2) -> TpPair (replace x t t1, replace x t t2)
  | _ -> t'



let rec tp_to_str (t:tp) : string = match t with 
  | TpBool -> "Bool"
  | TpNat -> "Nat"
  | TpUnit -> "Unit"
  | TpArr (t1, t2) -> "(" ^ (tp_to_str t1) ^ " -> " ^ (tp_to_str t2) ^ ")"
  | TpPair (t1, t2) -> "(" ^ (tp_to_str t1) ^ ", " ^ (tp_to_str t2) ^ ")"
  | TpVar x -> x
  | TpDef (x, t1) ->  "(" ^ x ^ " = " ^ (tp_to_str t1) ^ ")" 

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
(*printing *)



let print_constraints (constraints:constr) : unit = 
  List.iter (fun (s, t) -> Printf.printf "%s = %s\n" (tp_to_str s) (tp_to_str t)) constraints

let print_sigma (sigma:sigma) : unit =
List.iter (fun (x, t) -> Printf.printf "%s = %s\n" x (tp_to_str t)) sigma

let unify_print (constraints:constr) : unit =
  print_endline "Constraints:";
  print_constraints (constraints); 
  print_endline "\nUnification Result:";
  print_sigma (unify constraints)

let () = unify_print ([(TpVar "Y", TpPair (TpNat, TpBool)); (TpVar "X", TpArr (TpVar "Y", TpNat))])
                       