(* === DEFINITIONS === *)
type var_name = string 
type type_name = string  
type construct_name = string

type top_level = 
  | Definition of (var_name * tp) * term (* let x : T = t *)
  | TypeDefinition of (type_name * (construct_name * scheme list) list) 
   (* type <type_name> = 
      | <construct_name> of <tp list>
      | ... *)
and tp = 
  | TpBool | TpNat | TpUnit
  | TpArr of tp * tp    (* T1 -> T2 *)
  | TpPair of tp * tp   (* (T1, T2) *)
  | TpVar of type_name  (* type "X" -- will be inferred *)
  | TpDefined of type_name * (tp list)   (* top_level user defined type "X" -- concrete type *)
and term =
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
  (* λ Calculus *)
  | TmLam of (var_name * tp) * term 
  | TmApp of term * term
  | TmFix of (var_name * tp)  * term * term 
  (* Pairs *)
  | TmPair of term * term 
  | TmFst of term 
  | TmSnd of term
  (* If then else *)
  | TmIf of term * term * term 
  (* User defined types *)
  | TmConstructor of (construct_name * term list) (* constructor of type X *)
  (*pattern matching term*)
  | TmMatch of term * (pattern* term) list
  and pattern =
    | PVar of var_name 
    | PUnit
    | PTrue | PFalse
    | PZero
    | PFst | PSnd
    | PSucc of pattern
    | PPred of pattern
    | PPair of pattern * pattern
    | PConstructor of (construct_name * pattern list) (* constructor of type X *)
    | PElse 
 
and  scheme = Forall of (type_name list) * tp 

type context = (var_name * scheme) list
type constructs = (construct_name * type_name * (scheme list))  list 
type sigma  = (type_name * tp) list
type constr = (tp * tp) list 
type program = top_level list * term 

(* we infer the type of term given a top_level list of definitions *)

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
  | TpDefined (x, l) -> x ^ "(" ^ (String.concat ", " (List.map tp_to_str l)) ^ ")"
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
  | TmMatch (t, patterns) -> 
    let patterns_str = List.fold_right (fun (p, e) acc -> "\t| " ^ (pattern_to_str p) ^ " -> " ^ (term_to_str e) ^ "\n" ^ acc) patterns "" in
    "match " ^ (term_to_str t) ^ " with \n" ^ patterns_str
  | TmConstructor (construct_name, args) -> 
    let args_str = List.fold_right (fun arg acc -> (term_to_str arg) ^ ", " ^ acc) args "" in
    construct_name ^ "(" ^ (String.sub args_str 0 ((String.length args_str) - 2)) ^ ")"
  and pattern_to_str (p:pattern) : string = match p with
    | PVar x -> x
    | PUnit -> "unit"
    | PTrue -> "true"
    | PFalse -> "false"
    | PZero -> "zero"
    | PSucc p1 -> "succ (" ^ (pattern_to_str p1) ^ ")"
    | PPred p1 -> "pred (" ^ (pattern_to_str p1) ^ ")"
    | PPair (p1, p2) -> "<" ^ (pattern_to_str p1) ^ ", " ^ (pattern_to_str p2) ^ ">"
    | _ -> "??"
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
  | TpDefined (x, l) -> List.map (fun y -> fv_tp y) l |> List.flatten 
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
| TpDefined (y, inner_vars) -> if y = x then t else TpDefined (y, List.map (replace x t) inner_vars)
| TpArr (t1, t2) -> TpArr (replace x t t1, replace x t t2)
| TpPair (t1, t2) -> TpPair (replace x t t1, replace x t t2)
| _ -> t'
(* =============================== *)

let rec parse_top_level (l : top_level list) (cons_ctx: constructs) (var_ctx: context) : (constructs * context)  = 
  match l with
  | [] -> (cons_ctx, var_ctx) 
  | Definition ((x, t), e) :: rest -> 
    let var_ctx' = (x, Forall ([], t)) :: var_ctx in
      parse_top_level rest cons_ctx var_ctx'
  | TypeDefinition (tp_name, cons_list ):: rest -> 
    let x = parse_construct_list cons_list tp_name [] in
      parse_top_level rest  (x @ cons_ctx) var_ctx

and parse_construct_list (cons_list) (tp_name:type_name) (aux): constructs = 
   match cons_list with
   | [] -> [] 
   | (construct_name, args) :: rest -> 
      (construct_name, tp_name, args) :: parse_construct_list rest tp_name aux
(* =============================== *)



(* === CONSTRAINT GENERATION FUNCTIONS === *)
let rec generateconstraints (construct_list : constructs) (ctx : context) (tm : term) : tp * constr =
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
      let (typ, c) = generateconstraints construct_list ctx t1 
      in (TpNat, c @ [(typ, TpNat)]) (* enforce that t1: TpNat *)

  | TmPred t1 -> 
      let (typ, c) = generateconstraints construct_list ctx t1 
      in (TpNat, c @ [(typ, TpNat)])

  | TmIsZero t1 -> 
      let (typ, c) = generateconstraints construct_list ctx t1 
      in (TpBool, c @ [(typ, TpNat)]) (* enforce t1:TpNat and the result is a bool*)

  | TmLam((x, typ), t1) -> 
      let (t1_type, c) = generateconstraints construct_list ((x, Forall ([], typ)) :: ctx) t1 
      in (TpArr(typ, t1_type), c)

  | TmApp(t1, t2) -> 
      let (t1_type, c1) = generateconstraints construct_list ctx t1 in
      let (t2_type, c2) = generateconstraints construct_list ctx t2 in
      let f = TpVar (term_to_str(t1) ^ fresh_count() ^"_x_app") in  
      let c_app = [(t1_type, TpArr(t2_type, f))] in (f, c1 @ c2 @ c_app)

  | TmLet(x, t1, t2) -> 
      let (t1_type, c1) = generateconstraints construct_list ctx t1 in
      let f_scheme = generalize ctx t1_type in
      let f = TpVar x in
      let ctx' = (x, f_scheme) :: (remove_binding x ctx) in
      let (t2_type, c2) = generateconstraints construct_list ctx' t2 in
      let c_let = [(f, t1_type)] in
      (t2_type, c1 @ c_let @ c2)

  | TmPair(t1, t2) -> 
      let (ty1, c1) = generateconstraints construct_list ctx t1 in 
      let (ty2, c2) = generateconstraints construct_list ctx t2 in 
      (TpPair(ty1, ty2), c1 @ c2)

  | TmFst t1 ->  
      let (typ, c) = generateconstraints construct_list ctx t1 in
      let a = TpVar ((term_to_str t1) ^ fresh_count() ^ "_a_fst") 
      and b = TpVar ((term_to_str t1) ^ fresh_count() ^ "_b_fst") in
      let c_fst = [(typ, TpPair(a, b))] in  
      (a, c @ c_fst)

  | TmSnd t1 -> 
      let (typ, c) = generateconstraints construct_list ctx t1 in
      let a = TpVar  ((term_to_str t1) ^fresh_count() ^ "_a_snd") 
      and b = TpVar  ((term_to_str t1) ^fresh_count() ^ "_b_snd") in
      let c_snd = [(typ, TpPair(a, b))] in (b, c @ c_snd)

  | TmIf(cond, t1, t2) -> 
      let (cond_type, c_cond) = generateconstraints construct_list  ctx cond in
      let (t1_type, c1) = generateconstraints construct_list ctx t1 in
      let (t2_type, c2) = generateconstraints construct_list ctx t2 in
      (* Condition must be boolean and branches must have the same type *)
      let c_if = [(cond_type, TpBool); (t1_type, t2_type)] in
      (t1_type, c_cond @ c1 @ c2 @ c_if) 

  | TmMatch (t,patterns) -> 
      let (ty,ct) = generateconstraints construct_list ctx t in
      let rs = TpVar((term_to_str t) ^ fresh_count() ^ "match") in 
      let rec process_cases cases ctx constraints = 
        match cases with
        | [] -> []
        | (pat, e) :: rest -> 
          let (ctx', c_pat, pat_type) = generate_pattern_constraints ctx pat construct_list in
          let (e_type, c_e) = generateconstraints construct_list (ctx' @ ctx) e in
          let c_match = [(e_type, rs)] in  (* All branches must return same type *)
          c_pat @ c_e @ c_match @ process_cases rest ctx constraints in
          let constraints = process_cases patterns ctx [] 
          in (rs, ct @ constraints)

  | TmFix((x, typ), t1, t2) -> 
     let ctx' = (x, Forall ([], typ)) :: (remove_binding x ctx) in
     let (t1_type, c1) = generateconstraints construct_list ctx' t1 in
     let c_fix = [(t1_type, typ)] in
     let (t2_type, c2) = generateconstraints construct_list ctx' t2 in 
     (t2_type, c1 @ c_fix @ c2)

  | TmConstructor (construct_name, args) -> 
    let (_ , construct_type, arg_definitions) = List.find (fun (name, _, _) -> name = construct_name) construct_list in
    let (args_inferred_types, args_inner_constraints) = 
      List.split ( List.map (fun arg -> 
        let arg_inferred_type, c = generateconstraints construct_list ctx arg in
        (arg_inferred_type, c))  args )  in
   let inner_constraints = List.flatten args_inner_constraints in
   let instantiated_arg_defs = List.map (fun arg -> instantiate arg) arg_definitions in
   let args_constrains = List.map2  (fun x y -> (x, y)) args_inferred_types instantiated_arg_defs in
   (TpDefined (construct_type, args_inferred_types) , args_constrains @ inner_constraints )


and generate_pattern_constraints (ctx:context) (pat:pattern) constructs : context * constr * tp  =
  match pat with
  | PVar x -> ([(x, Forall ([], TpVar x))], [], TpVar x)
  | PUnit -> ([], [], TpUnit)
  | PTrue | PFalse -> ([], [], TpBool)
  | PFst -> ([], [], TpPair (TpVar "a", TpVar "b"))
  | PSnd -> ([], [], TpPair (TpVar "a", TpVar "b"))
  | PZero -> ([], [], TpNat) 
  | PElse -> ([], [], TpVar "a")
  | PSucc n  | PPred n ->let (ctx1, c1, t1) = generate_pattern_constraints ctx n constructs in
                            (ctx1, c1 @ [(t1, TpNat)], TpNat)
  | PPair (p1, p2) -> 
        let (ctx1, c1, t1) = generate_pattern_constraints ctx p1 constructs in
        let (ctx2, c2, t2) = generate_pattern_constraints ctx p2 constructs in
        (ctx1 @ ctx2, c1 @ c2, TpPair (t1, t2))
  | PConstructor (construct_name, patterns) -> 
        let (_, construct_type, arg_definitions) = List.find (fun (name, _, _) -> name = construct_name) constructs in
            let rec generate_arg_constraints patterns arg_definitions ctx =
              match (patterns, arg_definitions) with
              | [], [] -> (ctx, [], [])
              | (p :: ps), (arg_type :: ats) ->
                  let (ctx', c, t) = generate_pattern_constraints ctx p constructs in
                  let (ctx'', c', ts) = generate_arg_constraints ps ats ctx' in
                  (ctx'', c @ c', t :: ts)
              | _ -> raise (UnificationError ("Constructor arguments mismatch"))
            in
            let (final_ctx, constraints, argument_types) = generate_arg_constraints patterns arg_definitions ctx in
            let constructor_type = TpDefined(construct_name, argument_types) in
            (final_ctx, constraints, constructor_type)
and generalize (ctx:context) (t:tp) : scheme = (* REF : url1 *)
  let freevars_ctx = fv_ctx ctx in
  let freevars_tp = fv_tp t in
  let generalized_vars = List.filter (fun x -> not (List.mem x freevars_ctx)) freevars_tp in
  let unique_generalized_vars =  List.sort_uniq compare generalized_vars
  in Forall(unique_generalized_vars, t)
and remove_binding (x : type_name) (ctx : context) : context = (* REF : url1 *)
  List.filter (fun (y, _) -> y <> x) ctx
and instantiate (Forall (vars, t):scheme) : tp =  (* REF : url1 *)
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
    | TpDefined (x, inner_vars) -> 
              (match List.assoc_opt x subst_list with
                | Some tp -> tp
                | None -> (
                  let inner_vars_subst = List.map subst_tp inner_vars in
                  TpDefined (x, inner_vars_subst) )
                )
    | TpArr (t1, t2) -> TpArr (subst_tp t1, subst_tp t2)
    | TpPair (t1, t2) -> TpPair (subst_tp t1, subst_tp t2)
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
    match (s, t) with 
        | (TpDefined (x1, inner_vars1), TpDefined (x2, inner_vars2)) -> 
          (* if both are defined as the same , check if they are equal (including their inner vars )*)
            if x1 = x2 && (inner_vars_are_equal inner_vars1 inner_vars2) then  unify rest 
              else raise (UnificationError ("Unification failed: " ^ (tp_to_str s) ^ " = " ^ (tp_to_str t)) )
        | (s, t) when s = t -> unify rest (* BASE CASE  *)
        | (TpArr (s1, s2), TpArr (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpPair (s1, s2), TpPair (t1, t2)) -> unify ((s1, t1) :: (s2, t2) :: rest)
        | (TpVar x, t) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (t, TpVar x) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest)
        | (TpDefined (x, inner_vars), t) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest) 
        | (t, TpDefined (x, inner_vars)) when not (occurs x t) -> (x, t) :: unify (subst (x, t) rest) 
        | ( _ , _ ) -> raise (UnificationError ("Unification failed: " ^ (tp_to_str s) ^ " = " ^ (tp_to_str t)) )
and inner_vars_are_equal (i1:tp list) (i2:tp list) : bool = 
  try List.for_all2 (fun x y -> x = y) i1 i2 
          with Invalid_argument _ -> false
and occurs (x:type_name) (t:tp) : bool = (* X ∈ FV(T) *)
  match t with
  | TpVar y -> x = y
  | TpArr (t1, t2) -> occurs x t1 || occurs x t2
  | TpPair (t1, t2) -> occurs x t1 || occurs x t2
  | TpDefined (y, inner_vars) -> x = y || List.exists (occurs x) inner_vars
  | _ -> false
and subst ((x:type_name), (t:tp)) (constraints:constr) : constr =  (* [X/T] C *)
  List.map (fun (s, u) -> (replace x t s, replace x t u)) constraints
(* ================================ *)


(* === TYPE CHECKING PIPELINE === *)
let check_type (program:term) (intended_type:tp) : unit = 
  let (inferred_type, constraints) = generateconstraints [] [] program in
  let inferred_subs = unify constraints in
  let result_type = List.fold_right (fun (x, t_sub) acc -> replace x t_sub acc) inferred_subs inferred_type in
  if ((tp_to_str result_type) = (tp_to_str intended_type)) then 
    print_endline ("Type check successful: " ^ (tp_to_str intended_type) )
  else
    print_endline ("Type check failed: expected " ^ (tp_to_str intended_type) ^ " but got " ^ (tp_to_str result_type))
(* =============================== *)


let check_program ((top_list , main):program) (intended_type:tp) : unit = 
  let (constructs, ctx) = parse_top_level top_list [] [] in
  let (inferred_type, constraints) = generateconstraints constructs ctx main in
  let inferred_subs = unify constraints in
  let result_type = List.fold_right (fun (x, t_sub) acc -> replace x t_sub acc) inferred_subs inferred_type in
  if ((tp_to_str result_type) = (tp_to_str intended_type)) then 
  print_endline ("Type check successful: " ^ (tp_to_str intended_type) )
else
  print_endline ("Type check failed: expected " ^ (tp_to_str intended_type) ^ " but got " ^ (tp_to_str result_type))
  

  (* === Examples === *)

(* for(i) = if (iszero i) then Unit else for(pred i) *)
let () = print_string ("Recursion example: for loop \n\t")
let rec_prog = TmFix ( ("for", TpArr (TpNat, TpUnit)) , 
TmLam (("i", TpNat), 
TmIf (TmIsZero (TmVar "i"), TmUnit, TmApp (TmVar "for", TmPred (TmVar "i"))) ), 
TmApp (TmVar "for", TmSucc (TmSucc (TmZero))) )
let () = check_type rec_prog TpUnit

(*  (some 0 , some true) *)
let () = print_string ("User defined polymorphic example: option \n\t")
let () = 
let prog : program = 
  [TypeDefinition ("Option", 
    ["Some", [Forall (["X"], TpVar "X")];
     "None", [Forall ([], TpUnit)]])], 
  TmPair (TmConstructor ("Some", [TmZero]), 
          TmConstructor  ("Some", [TmTrue]))

in check_program prog 
  (TpPair (TpDefined ("Option", [TpNat]), 
           TpDefined ("Option", [TpBool])))

let () = print_string ("Pattern matching: isZero functionality  \n\t")
let () = 
  let prog : program = [], 
    TmLet ("x", TmSucc (TmZero), 
    TmMatch (TmVar "x", 
    [(PZero, TmTrue); 
    (PSucc (PVar "y"), TmFalse)]))
  in check_program prog TpBool




(* identity function polymorphism *)
let () = print_string ("Polymorphism: identity function  \n\t")

let () = 
let prog : program = [], 
    TmLet ("id",  TmLam (("x", TpVar "X"), TmVar "x"), 
    TmPair (TmApp (TmVar "id", TmZero), TmApp (TmVar "id", TmTrue)))
in check_program prog (TpPair(TpNat , TpBool))



(* pattern matching on some *)
let () = print_string ("Pattern matching on user defined types  \n\t")
let () =
  let prog  = 
    [TypeDefinition ("Option", 
      ["Some", [Forall (["X"], TpVar "X")];
       "None", [Forall ([], TpUnit)]])], 
    TmMatch (TmConstructor ("Some", [TmZero]), 
    [(PConstructor ("Some", [PVar "x"]), TmVar "x"); 
     (PElse, TmUnit)])
in check_program prog (TpUnit)



(* 'a tree *)
let () = print_string ("Polymorphic tree example  \n\t")
let x_def = 
  TypeDefinition ("XTree", [
    ("Leaf",[Forall(["X"], TpVar "X")]);
    ("Node",[Forall(["X"], TpPair
           (TpDefined ("XTree", [TpVar "X"]),
            TpDefined ("XTree", [TpVar "X"]))
      )])])
let prog = [x_def],   TmPair (TmConstructor ("Leaf", [TmZero]), TmConstructor ("Leaf", [TmFalse]))
 
let () = check_program prog (TpPair (TpDefined ("XTree", [TpNat]), TpDefined ("XTree", [TpBool])))


(* nat tree *)
let nat_def = 
  TypeDefinition ("NatTree", [
    ("Leaf",[Forall([], TpNat)]);
    ("Node",[Forall([], TpPair
           (TpDefined ("NatTree", []),
            TpDefined ("NatTree", []))
      )])])
  
  
let prog = [nat_def],   TmPair (TmConstructor ("Leaf", [TmZero]), TmConstructor ("Leaf", [TmSucc (TmZero)]))



let () = print_string ("Pattern matching: natural numify \n\t")

let prog =
  [TypeDefinition ("code", [
    ("nat", [Forall ([], TpNat)]);
    ("bool",[Forall ([], TpBool)])
  ])],
  TmMatch (TmConstructor ("nat", [TmZero]), [
    (PConstructor ("nat", [PVar "X"]), TmVar "X"); 
    (PConstructor ("bool",[PFalse]), TmZero); 
    (PConstructor ("bool",[PTrue]), TmSucc TmZero);
  ])

let () = check_program prog TpNat