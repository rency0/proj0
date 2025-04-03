# Terms and Types Printing Test
```ocaml 
(* print all possible terms *)
let () = let all_terms = [ 
    TmUnit; TmTrue; TmFalse; TmZero; TmVar "x"; 
    TmLet ("x", TmTrue, TmFalse); 
    TmIsZero (TmZero); 
    TmSucc (TmZero); 
    TmPred (TmZero); 
    TmApp (TmLam (("x", TpNat), TmVar "x"), TmZero); 
    TmFst (TmPair (TmTrue, TmFalse)); 
    TmSnd (TmPair (TmTrue, TmFalse)); 
    TmIf (TmTrue, TmFalse, TmUnit) ] 
  in List.iter (fun t -> Printf.printf "%s\n" (term_to_str t)) all_terms; print_endline ""

(* Print all possible types *)
let () = let all_types = [
    TpBool; TpNat; TpUnit; 
    TpArr (TpNat, TpBool); 
    TpPair (TpNat, TpBool); 
    TpVar "X"; 
    TpDef ("List", TpPair (TpVar "X", TpVar "X")) ] 
  in List.iter (fun t -> Printf.printf "%s\n" (tp_to_str t)) all_types; print_endline ""
  
```

# Unify all branches testing 
```ocaml 
let () =  unify_print ([
  
(* (Bool -> Unit, Y) = ( Y -> Unit, X)  *)  
((TpPair(TpArr(TpBool, TpUnit), TpVar "Y")), 
((TpPair(TpArr(TpVar "Y", TpUnit), TpVar "X")))); 

(* Var "A" = Def "B":Nat ; A->C = A->Bool *)
(TpVar "A", TpDef ("B", TpNat));
(TpArr (TpVar "A", TpVar "C"), TpArr (TpVar "B", TpBool)); 

(* Var "D" = Var "E" *)
(TpVar "D", TpVar "E"); (TpVar "D", TpBool) ; 
 
(* Def "Z" := "A"->"C", Var "Z" *)
(TpDef ("Z", TpArr (TpVar "A", TpVar "C")), TpVar "Z"); 

]) 


let () = unify_print ([
  (TpVar "D", TpVar "E"); (TpVar "D", TpBool) ; (TpNat, TpVar "E")
])

```

# Non-inclusive Constraint generation successful testing 
```ocaml

(* inc=λx.(s x) ; p=(T, 0) ; if (p.fst) then (inc p.snd) else (inc (inc p.snd))*)
let program =   
  TmLet ("inc",
    TmLam (("x", TpNat), TmSucc (TmVar "x")),
  TmLet ("p",
    TmPair (TmTrue, TmZero),
  TmIf (TmFst (TmVar "p"),
    TmApp (TmVar "inc", TmSnd (TmVar "p")),
    TmApp (TmVar "inc", TmApp( TmVar "inc", TmSnd (TmVar "p"))))))
let (final_type, constraints) =  (generateconstraints [] program)
let () = unify_print constraints


(* x=(0 , 1) ; y=(T, F) ; if (x.fst == 0) then y.fst else y.snd*)
let program = TmLet ("x", TmPair (TmZero, TmSucc (TmZero)) , 
              TmLet("y" , TmPair(TmTrue, TmFalse), 
              TmIf (TmIsZero (TmFst (TmVar "x")), TmFst (TmVar "y"), TmSnd (TmVar "y"))))

let (final_type, constraints) =  (generateconstraints [] program)
let () = unify_print constraints


(* x=0 ; p=(x, x) ; lambda y : (A, A) = if (y.fst iszero) then (y.snd) else 0 *)
let program = 
  TmLet ("x", TmZero, 
  TmLet ("p", TmPair (TmVar "x", TmVar "x"), 
  TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
  TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero))))
let (final_type, constraints) =  (generateconstraints [] program)
let () = unify_print constraints

```