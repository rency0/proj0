
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
  