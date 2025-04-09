(* url1==https://www.researchgate.net/publication/2528716_Generalizing_Hindley-Milner_Type_Inference_Algorithms *)

(* === DEFINITIONS === *)
type var_name = string 
type type_name = string  

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
  | TmLam of (var_name * tp) * term (*THINK: maybe don't need type in λ (x:T) . t*)(* todo : rm type of lam *)
  | TmApp of term * term
  | TmFix of (var_name * tp)  * term * term 
  (* Pairs *)
  | TmPair of term * term 
  | TmFst of term 
  | TmSnd of term
  (* If then else *)
  | TmIf of term * term * term 
  (*pattern matching term*)
  | TmMatch of term * (pattern* term) list
  | TmTypedef of (type_name * tp) * term (* define type X = T in t1 *)
  and pattern =
    | PVar of var_name 
    | PUnit
    | PTrue | PFalse
    | PZero
    | PSucc of pattern
    | PPred of pattern
    | PPair of pattern * pattern

type scheme = Forall of (type_name list) * tp 
type context = (var_name * scheme) list
type sigma  = (type_name * tp) list
type constr = (tp * tp) list 

exception UnificationError of string
(* =============================== *)


(* === PRINTING AND TO STRING === *)
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
  | TmMatch (t, patterns) -> 
    let patterns_str = List.fold_right (fun (p, e) acc -> "\t| " ^ (pattern_to_str p) ^ " -> " ^ (term_to_str e) ^ "\n" ^ acc) patterns "" in
    "match " ^ (term_to_str t) ^ " with \n" ^ patterns_str
  and pattern_to_str (p:pattern) : string = match p with
    | PVar x -> x
    | PUnit -> "unit"
    | PTrue -> "true"
    | PFalse -> "false"
    | PZero -> "zero"
    | PSucc p1 -> "succ (" ^ (pattern_to_str p1) ^ ")"
    | PPred p1 -> "pred (" ^ (pattern_to_str p1) ^ ")"
    | PPair (p1, p2) -> "<" ^ (pattern_to_str p1) ^ ", " ^ (pattern_to_str p2) ^ ">"
let print_constraints (constraints:constr) : unit = 
  List.iter (fun (s, t) -> Printf.printf "%s = %s\n" (tp_to_str s) (tp_to_str t)) constraints
let print_sigma (sigma:sigma) : unit =
  List.iter (fun (x, t) -> Printf.printf "%s = %s\n" x (tp_to_str t)) sigma
let print_ctx (ctx:context) : unit =
  List.iter (fun (x, scheme) -> Printf.printf "%s = %s\n" x (match scheme with Forall (vars, t) -> tp_to_str t)) ctx
(* =============================== *)

(* === LIST FREE VARIABLES === *)
let rec fv_tp (t:tp) : type_name list = 
  match t with
  | TpArr (t1, t2) -> (fv_tp t1) @ (fv_tp t2)
  | TpPair (t1, t2) -> (fv_tp t1) @ (fv_tp t2)
  | TpVar x -> [x] 
  | TpDef (x, t1) -> x :: (fv_tp t1)
  | _ -> []
let fv_scheme (Forall((vars:type_name list), (t:tp))) : type_name list = 
  List.filter (fun x -> not (List.mem x vars)) (fv_tp t)
let fv_ctx (ctx:context) : type_name list = 
  List.fold_left (fun acc (_, scheme) -> 
    List.fold_left (fun acc x -> 
      if List.mem x acc then acc else x::acc) acc (fv_scheme scheme)) [] ctx
(* =============================== *)


(* === SUBSTITUTION FUNCTION === *)
let rec replace (x:type_name) (t:tp) (t':tp) : tp  = (* [X/T] T' *) (* REF: tb section 22.1.1 *)
match t' with
| TpVar y -> if y = x then t else t' 
| TpDef (y, t1) -> if y = x then t else TpDef (y, replace x t t1) 
| TpArr (t1, t2) -> TpArr (replace x t t1, replace x t t2)
| TpPair (t1, t2) -> TpPair (replace x t t1, replace x t t2)
| _ -> t'
(* =============================== *)


(* === CONSTRAINT GENERATION FUNCTIONS === *)
let rec generateconstraints (ctx : context) (tm : term) : tp * constr =
  match tm with
  | TmVar x ->( 
      match List.assoc_opt x ctx with
      | Some scheme -> (instantiate scheme, [])
      | None ->  raise (UnificationError ("Variable "^ x ^" not found")))

  | TmUnit ->  (TpUnit, [])
  | TmTrue ->  (TpBool, [])
  | TmFalse -> (TpBool, [])
  | TmZero ->  (TpNat, [])

  | TmSucc t1 -> 
      let (typ, c) = generateconstraints ctx t1 
      in (TpNat, c @ [(typ, TpNat)]) (* enforce that t1: TpNat *)

  | TmPred t1 -> 
      let (typ, c) = generateconstraints ctx t1 
      in (TpNat, c @ [(typ, TpNat)])

  | TmIsZero t1 -> 
      let (typ, c) = generateconstraints ctx t1 
      in (TpBool, c @ [(typ, TpNat)]) (* enforce t1:TpNat and the result is a bool*)

  | TmLam((x, typ), t1) -> 
      let (t1_type, c) = generateconstraints ((x, Forall ([], typ)) :: ctx) t1 
      in (TpArr(typ, t1_type), c)

  | TmApp(t1, t2) -> 
      let (t1_type, c1) = generateconstraints ctx t1 in
      let (t2_type, c2) = generateconstraints ctx t2 in
      let f = TpVar (term_to_str(t1) ^ fresh_count() ^"_x_app") in  
      let c_app = [(t1_type, TpArr(t2_type, f))] in (f, c1 @ c2 @ c_app)

  | TmLet(x, t1, t2) -> 
      let (t1_type, c1) = generateconstraints ctx t1 in
      let f_scheme = generalize ctx t1_type in
      let f = TpVar x in
      let ctx' = (x, f_scheme) :: (remove_binding x ctx) in
      let (t2_type, c2) = generateconstraints ctx' t2 in
      let c_let = [(f, t1_type)] in
      (t2_type, c1 @ c_let @ c2)

  | TmPair(t1, t2) -> 
      let (ty1, c1) = generateconstraints ctx t1 in 
      let (ty2, c2) = generateconstraints ctx t2 in 
      (TpPair(ty1, ty2), c1 @ c2)

  | TmFst t1 ->  
      let (typ, c) = generateconstraints ctx t1 in
      let a = TpVar ((term_to_str t1) ^ fresh_count() ^ "_a_fst") 
      and b = TpVar ((term_to_str t1) ^ fresh_count() ^ "_b_fst") in
      let c_fst = [(typ, TpPair(a, b))] in  (a, c @ c_fst)

  | TmSnd t1 -> 
      let (typ, c) = generateconstraints ctx t1 in
      let a = TpVar  ((term_to_str t1) ^fresh_count() ^ "_a_snd") 
      and b = TpVar  ((term_to_str t1) ^fresh_count() ^ "_b_snd") in
      let c_snd = [(typ, TpPair(a, b))] in (b, c @ c_snd)

  | TmIf(cond, t1, t2) -> 
      let (cond_type, c_cond) = generateconstraints ctx cond in
      let (t1_type, c1) = generateconstraints ctx t1 in
      let (t2_type, c2) = generateconstraints ctx t2 in
      (* Condition must be boolean and branches must have the same type *)
      let c_if = [(cond_type, TpBool); (t1_type, t2_type)] in
      (t1_type, c_cond @ c1 @ c2 @ c_if) 

  | TmMatch (t,patterns) -> 
      let (ty,ct) = generateconstraints ctx t in
      let rs = TpVar((term_to_str t) ^ fresh_count() ^ "match") in 
      let rec process_cases cases ctx constraints = 
        match cases with
        | [] -> []
        | (pat, e) :: rest -> 
          let (ctx', c_pat, pat_type) = generate_pattern_constraints ctx pat in
          let (e_type, c_e) = generateconstraints (ctx' @ ctx) e in
          let c_match = [(e_type, rs)] in  (* All branches must return same type *)
          c_pat @ c_e @ c_match @ process_cases rest ctx constraints in
          let constraints = process_cases patterns ctx [] 
          in (rs, ct @ constraints)

  | TmFix((x, typ), t1, t2) -> 
     let ctx' = (x, Forall ([], typ)) :: (remove_binding x ctx) in
     let (t1_type, c1) = generateconstraints ctx' t1 in
     let c_fix = [(t1_type, typ)] in
     let (t2_type, c2) = generateconstraints ctx' t2 in 
     (t2_type, c1 @ c_fix @ c2)

  | TmTypedef ((typ_name, typ) , t) ->
      let (t_typ ,c) = generateconstraints ctx t in 
      ( t_typ , ((TpVar typ_name, typ)::c ))
and generate_pattern_constraints (ctx:context) (pat:pattern) : context * constr * tp  =
  match pat with
  | PVar x -> ([(x, Forall ([], TpVar x))], [], TpVar x)
  | PUnit -> ([], [], TpUnit)
  | PTrue | PFalse -> ([], [], TpBool)
  | PZero -> ([], [], TpNat) 
  | PSucc n  | PPred n ->let (ctx1, c1, t1) = generate_pattern_constraints ctx n in
                            (ctx1, c1 @ [(t1, TpNat)], TpNat)
  | PPair (p1, p2) -> 
        let (ctx1, c1, t1) = generate_pattern_constraints ctx p1 in
        let (ctx2, c2, t2) = generate_pattern_constraints ctx p2 in
        (ctx1 @ ctx2, c1 @ c2, TpPair (t1, t2))
and generalize (ctx:context) (t:tp) : scheme = (* REF : url1 *)
  let freevars_ctx = fv_ctx ctx in
  let freevars_tp = fv_tp t in
  let generalized_vars = List.filter (fun x -> not (List.mem x freevars_ctx)) freevars_tp in
  let unique_generalized_vars =  List.sort_uniq compare generalized_vars
  in Forall(unique_generalized_vars, t)
and remove_binding (x : type_name) (ctx : context) : context = (* REF : url1 *)
  List.filter (fun (y, _) -> y <> x) ctx
and instantiate (Forall (vars, t):scheme) =  (* REF : url1 *)
  let get_fresh vars = List.map (fun var -> TpVar (var^fresh_count())) vars in  
  let fresh_vars = get_fresh vars in
  let subst_list = List.combine vars fresh_vars in 
  let rec subst_tp t  = 
    match t with 
    | TpBool | TpNat | TpUnit -> t
    | TpVar x ->
        (match List.assoc_opt x subst_list with
          | Some tp -> tp
          | None -> TpVar x)
    | TpArr (t1, t2) -> TpArr (subst_tp t1, subst_tp t2)
    | TpPair (t1, t2) -> TpPair (subst_tp t1, subst_tp t2)
    | TpDef (x, t1) -> TpDef (x, subst_tp t1)
  in  subst_tp t 
and fresh_count  = 
  let count = ref 0 in
  fun () -> let c = !count in count := c + 1; string_of_int c
(* ================================ *)
  

(* === UNIFICATION FUNCTION === *)
let rec unify (constraints:constr) : sigma =
  match constraints with
  | [] -> []
  | (s, t) :: rest -> 
    if s = t then unify rest
    else match (s, t) with 
        | (TpArr (s1, s2), TpArr (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpPair (s1, s2), TpPair (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpDef (x, s), t) -> unify ((TpVar x, s) :: (TpVar x , t) :: rest )
        | (t, TpDef (x, s)) -> unify ((TpVar x, s) :: (TpVar x , t) :: rest )
        | (TpVar x, t) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (t, TpVar x) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | ( _ , _ ) -> raise (UnificationError ("Unification failed: " ^ (tp_to_str s) ^ " = " ^ (tp_to_str t)) )
and occurs (x:type_name) (t:tp) : bool = (* X ∈ FV(T) *)
  match t with
  | TpVar y -> x = y
  | TpArr (t1, t2) -> occurs x t1 || occurs x t2
  | TpPair (t1, t2) -> occurs x t1 || occurs x t2
  | TpDef (y, t1) -> x = y || occurs x t1
  | _ -> false
and subst ((x:type_name), (t:tp)) (constraints:constr) : constr =  (* [X/T] C *)
  List.map (fun (s, u) -> (replace x t s, replace x t u)) constraints
(* ================================ *)


(* === TYPE CHECKING PIPELINE === *)
let check_type (program:term) (intended_type:tp) : unit = 
  let (inferred_type, constraints) = generateconstraints [] program in
  let inferred_subs = unify constraints in
  let result_type = List.fold_right (fun (x, t_sub) acc -> replace x t_sub acc) inferred_subs inferred_type in
  if ((tp_to_str result_type) = (tp_to_str intended_type)) then 
    print_endline ("Type check successful: " ^ (tp_to_str intended_type) )
  else
    print_endline ("Type check failed: expected " ^ (tp_to_str intended_type) ^ " but got " ^ (tp_to_str result_type))
(* =============================== *)

(* ======================================================= *)
let x = ref 0 
let print_count () = 
  print_endline "----------------"; 
  print_int !x ; 
  print_newline () ;
  x := !x +1


(* let id = fun x -> x in (id 0 , id true )   *)
let program = 
  TmLet ("id",  TmLam (("x", TpVar "X"), TmVar "x"), 
  TmPair (TmApp (TmVar "id", TmZero), TmApp (TmVar "id", TmTrue)))

let () =print_count(); check_type program (TpPair(TpNat, TpBool));;

(* inc=λx.(s x) ; p=(T, 0) ; if (p.fst) then (inc p.snd) else (inc (inc p.snd))*)
let program =   
TmLet ("inc",
  TmLam (("x", TpNat), TmSucc (TmVar "x")),
TmLet ("p",
  TmPair (TmTrue, TmZero),
TmIf (TmFst (TmVar "p"),
  TmApp (TmVar "inc", TmSnd (TmVar "p")),
  TmApp (TmVar "inc", TmApp( TmVar "inc", TmSnd (TmVar "p"))))))
let () = print_count();  check_type program (TpNat)

(* x=(0 , 1) ; y=(T, F) ; if (x.fst == 0) then y.fst else y.snd*)
let program = TmLet ("x", TmPair (TmZero, TmSucc (TmZero)) , 
            TmLet("y" , TmPair(TmTrue, TmFalse), 
            TmIf (TmIsZero (TmFst (TmVar "x")), TmFst (TmVar "y"), TmSnd (TmVar "y"))))
let () = print_count() ; check_type program (TpBool)

(* x=0 ; p=(x, x) ; lambda y : (A, A) = if (y.fst iszero) then (y.snd) else 0 *)
let program = 
TmLet ("x", TmZero, 
TmLet ("p", TmPair (TmVar "x", TmVar "x"), 
TmApp ( 
  TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
  TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero)), 
TmVar "p")))
let () = print_count(); check_type program TpNat;;


(* inc=λx.(s x) ; p=(T, 0) ; if (p.fst) then (inc p.snd) else (inc (inc p.snd))*)
let program =   
TmLet ("inc",
  TmLam (("x", TpNat), TmSucc (TmVar "x")),
TmLet ("p",
  TmPair (TmTrue, TmZero),
TmIf (TmFst (TmVar "p"),
  TmApp (TmVar "inc", TmSnd (TmVar "p")),
  TmApp (TmVar "inc", TmApp( TmVar "inc", TmSnd (TmVar "p"))))))

let () = print_count();  check_type program (TpNat)

(* x=(0 , 1) ; y=(T, F) ; if (x.fst == 0) then y.fst else y.snd*)
let program = TmLet ("x", TmPair (TmZero, TmSucc (TmZero)) , 
TmLet("y" , TmPair(TmTrue, TmFalse), 
TmIf (TmIsZero (TmFst (TmVar "x")), TmFst (TmVar "y"), TmSnd (TmVar "y"))))

let () = print_count(); check_type program (TpBool)

(* x=0 ; p=(x, x) ; lambda y : (A, A) = if (y.fst iszero) then (y.snd) else 0 *)
let program = 
TmLet ("x", TmZero, 
TmLet ("p", TmPair (TmVar "x", TmVar "x"),
TmApp ((
  TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
  TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero))), 
  TmVar "p")))

let () = print_count(); check_type program (TpNat)

(* ------ *)
let test_term = 
TmMatch (
  TmPair (TmSucc TmZero, TmTrue), (* term we are matching on *)
  [
    (PPair (PVar "x", PFalse), TmFalse);                 (* doesn't match *)
    (PPair (PSucc PZero, PTrue), TmTrue);                (* matches *)             
  ]
)

let () = print_count(); check_type program (TpBool) ; print_endline "<<<"

(* ------ *)
let prog = TmTypedef (("natPair", TpPair (TpNat, TpNat)), 
  TmLam (("p", TpVar "natPair"),  TmTrue ))

let () = print_count(); check_type prog  (TpArr ( TpPair (TpNat, TpNat), TpBool) )

(* ------ *)
let prog = TmTypedef (("natPair", TpPair (TpNat, TpNat)), 
TmLet ("fst", TmLam (("p", TpVar "natPair") , TmFst (TmVar "p")), 
TmApp( TmVar "fst", TmPair (TmZero, TmZero)) ))

let () = print_count(); check_type prog  (TpNat) ; print_endline "<<<"

(* ------ *)


(* for(i) = if (iszero i) then Unit else for(pred i)*)
let rec_prog = TmFix ( ("for", TpArr (TpNat, TpUnit)) , 
TmLam (("i", TpNat), 
TmIf (TmIsZero (TmVar "i"), TmUnit, TmApp (TmVar "for", TmPred (TmVar "i"))) ), 
TmApp (TmVar "for", TmSucc (TmSucc (TmZero))) )

let () = print_count(); check_type rec_prog TpUnit


(* let x=2 in 
let y=3 in 
let add=(λp:(Nat, Nat) if iszero p.fst then p.snd else add (pred p.fst) (succ p.snd)) in
add ( x, y) *)

let program = TmFix ( ("add", TpArr ( TpPair(TpNat,TpNat), TpNat)) , 
TmLam ( ("pair", TpPair(TpNat,TpNat) ),
TmIf (TmIsZero (TmFst (TmVar "pair")), 
                TmSnd (TmVar "pair"), 
                TmApp (TmVar "add", (TmPair (TmPred (TmFst (TmVar "pair")), TmSucc (TmSnd (TmVar "pair")))) ))
                ), TmApp (TmVar "add",  TmPair ((TmSucc (TmSucc (TmZero))), (TmSucc (TmSucc (TmSucc (TmZero)))))))
                

let () = print_count(); check_type program TpNat
      
      
let prog = 
TmLet ("x", TmFalse, 
TmLet ("p", TmPair (TmVar "x", TmVar "x"),
TmLet ("nat", (
  TmApp ((
    TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
    TmIf (TmFst (TmVar "y"), TmSnd (TmVar "y"), TmFalse))), 
    TmPair (TmFalse, TmTrue))), 
  TmApp ((
      TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
      TmIf (TmFst (TmVar "y"), TmVar "nat", TmZero))), 
      TmVar "p" ))))

let () = print_count(); check_type prog (TpNat)



let program = 
  TmLet ("id",  TmLam (("x", TpVar "X"), TmVar "x"), 
  TmPair (TmApp (TmVar "id", TmZero), TmApp (TmVar "id", TmTrue)))
let() = print_count(); check_type program (TpPair(TpNat , TpBool))
