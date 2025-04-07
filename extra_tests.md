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


# Pretty printing constraint to unification 
```ocaml 
(* pretty printing functions *)
  let unify_print (constraints:constr) : unit =
    print_endline "Constraints:";
    print_constraints (constraints); 
    print_endline "\nUnification Result:";
    print_sigma (unify constraints)
(* -------------------------- *)
```

# TypeCheck program 

(* inc=λx.(s x) ; p=(T, 0) ; if (p.fst) then (inc p.snd) else (inc (inc p.snd))*)
let program =   
  TmLet ("inc",
    TmLam (("x", TpNat), TmSucc (TmVar "x")),
  TmLet ("p",
    TmPair (TmTrue, TmZero),
  TmIf (TmFst (TmVar "p"),
    TmApp (TmVar "inc", TmSnd (TmVar "p")),
    TmApp (TmVar "inc", TmApp( TmVar "inc", TmSnd (TmVar "p"))))))

let () = check_type program (TpNat)
(* -------------------------  *)

(* x=(0 , 1) ; y=(T, F) ; if (x.fst == 0) then y.fst else y.snd*)
let program = TmLet ("x", TmPair (TmZero, TmSucc (TmZero)) , 
TmLet("y" , TmPair(TmTrue, TmFalse), 
TmIf (TmIsZero (TmFst (TmVar "x")), TmFst (TmVar "y"), TmSnd (TmVar "y"))))

let () = check_type program (TpBool)
(* -------------------------  *)

(* x=0 ; p=(x, x) ; lambda y : (A, A) = if (y.fst iszero) then (y.snd) else 0 *)
let program = 
  TmLet ("x", TmZero, 
  TmLet ("p", TmPair (TmVar "x", TmVar "x"),
  TmApp ((
    TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
    TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero))), 
    TmVar "p")))
  
let () = check_type program (TpNat)
(* -------------------------  *)


# Typdef testing 
```ocaml
let prog = TmTypedef (("natPair", TpPair (TpNat, TpNat)), 
    TmLam (("p", TpVar "natPair"),  TmTrue ))
  
let () = check_type prog  (TpArr ( TpPair (TpNat, TpNat), TpBool) )


let prog = TmTypedef (("natPair", TpPair (TpNat, TpNat)), 
TmLet ("fst", TmLam (("p", TpVar "natPair") , TmFst (TmVar "p")), 
TmApp( TmVar "fst", TmPair (TmZero, TmZero)) ))

let () = check_type prog  (TpNat)

```

# Rec testing 
```ocaml 



(* for(i) = if (iszero i) then Unit else for(pred i)*)

let rec_prog = TmFix ( ("for", TpArr (TpNat, TpUnit)) , 
TmLam (("i", TpNat), 
TmIf (TmIsZero (TmVar "i"), TmUnit, TmApp (TmVar "for", TmPred (TmVar "i"))) ), 
TmApp (TmVar "for", TmSucc (TmSucc (TmZero))) )

let () = check_type rec_prog TpUnit

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
                  

                  let () = check_type program TpNat
                  
                  
                
```



# FUTURE TEST 
``` ocaml 
let program = 
  TmLet ("x", TmZero, 
  TmLet ("p", TmPair (TmVar "x", TmVar "x"),
  TmLet ("nat", (
    TmApp ((
      TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
      TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero))), 
      TmVar "p")), 
      TmApp ((
        TmLam (("y", TpPair (TpVar("A"),TpVar("A"))), 
        TmIf (TmIsZero (TmFst (TmVar "y")), TmSnd (TmVar "y"), TmZero))), 
        TmPair(TmFalse, TmTrue))) ))
  
let () = check_type program (TpBool)

```
(* -------------------------  *)