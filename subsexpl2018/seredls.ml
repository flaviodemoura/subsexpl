(**********************************************************)
(*                       SUBSEXPL                         *)
(* Step by step simulation of the reduction in explicit   *)
(* substitution calculi:  suspension calculus, lambda s_e *)
(* calculus and lambda sigma calculus                     *)
(*                                                        *)
(* Group of Theory of Computation,                        *)
(* Universidade de Brasilia - Brasil                      *)
(* ULTRA group,                                           *)
(* Heriot-Watt University  - UK                           *)
(* Authors: Flavio L. C. de Moura, Mauricio Ayala-Rincon  *) 
(*          and F. Kamareddine.                           *)
(*                                                        *)
(* Permission to copy and reuse this file mantaining its  *)
(* procedence indicated above                             *)
(**********************************************************)

(** This module contains the implementation of the reduction rules of the lambda sigma calculus.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open List
open Setypes

(** Implementation of the Beta rule. This rule starts the simulation of one step of beta reduction. *)
let rec betareduction1 exp pr = 
  match pr with 
    | []   -> (match exp with 
                 | A(L(e1,_,_),e2) -> Sb(e1,Pt(e2,Id)) 
                 | _ -> exp)
    | 1 :: tail -> (match exp with  
		      | Dummy         -> exp
		      | One           -> exp 
		      | Vr c          -> exp
		      | A(e1,e2)      -> A((betareduction1 e1 tail),e2)
		      | L(e1,variable_name,lambda_type)         -> L(betareduction1 e1 tail,variable_name,lambda_type) 
		      | Sb(e1,s2)     -> Sb((betareduction1 e1 tail),s2)
		      | _ -> assert false)  
    | 2 :: tail -> (match exp with
		      | Dummy          -> exp
		      | One            -> exp
		      | Vr c           -> exp
		      | L(e1,_,_)          -> exp
		      | A(e1,e2)       -> A(e1,(betareduction1 e2 tail))
		      | Sb(e1,s2)      -> Sb(e1,(betareduction1Sb s2 tail))
		      | _ -> assert false) 
    | _ -> exp
and  
  betareduction1Sb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((betareduction1Sb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((betareduction1 e1 tail),s2))
    | 2 :: tail -> (match subs with   
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(betareduction1Sb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(betareduction1Sb s2 tail)))
    | _ -> subs
        
(** Implementation of the App rule. This rule propagates a substitution over an application. *)
let rec appreduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | Sb(A(e1,e2),sb) -> A(Sb(e1,sb),Sb(e2,sb)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with  
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((appreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(appreduction e1 tail, variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((appreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(appreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(appreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  appreductionSb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((appreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((appreduction e1 tail),s2)) 
    | 2 :: tail -> (match subs with   
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(appreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(appreductionSb s2 tail)))
    | _ -> subs
        
(** Implementation of the Abs rule. This rule propagates a substitution over an abstraction. *)
let rec absreduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | Sb(L(e1,variable_name,lambda_type),sb) -> L(Sb(e1,Pt(One,Cp(sb,Up))),variable_name,lambda_type) 
               | _ -> exp)
    | 1 :: tail -> (match exp with  
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((absreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(absreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((absreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(absreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(absreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  absreductionSb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((absreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((absreduction e1 tail),s2))
    | 2 :: tail -> (match subs with   
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(absreductionSb s2 tail))
                      | Pt(e1,s2)     -> Pt(e1,(absreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the Clos rule. This rule composes substitutions. *)
let rec closreduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | Sb(Sb(e1,s1),s2) -> Sb(e1,Cp(s1,s2)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with  
	              | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((closreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(closreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((closreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(closreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(closreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  closreductionSb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((closreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((closreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(closreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(closreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the VarsCons rule. *)
let rec varconsreduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | Sb(One,Pt(e1,sb)) -> e1 
               | _ -> exp)
    | 1 :: tail -> (match exp with  
		      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((varconsreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(varconsreduction e1 tail, variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((varconsreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(varconsreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(varconsreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  varconsreductionSb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((varconsreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((varconsreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(varconsreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(varconsreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the Id rule. *)
let rec idreduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | Sb(e1,Id) -> e1 
               | _ -> exp)
    | 1 :: tail -> (match exp with  
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((idreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(idreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((idreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
	              | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(idreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(idreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  idreductionSb subs pr = 
  match pr with
    | [] -> subs
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((idreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((idreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(idreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(idreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the Assoc rule: associativity of the composition of substitutions. *)
let rec assocreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((assocreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(assocreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((assocreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(assocreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(assocreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  assocreductionSb subs pr = 
  match pr with
    | [] -> (match subs with 
               | Cp(Cp(s1,s2),t) -> Cp(s1,Cp(s2,t)) 
               | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((assocreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((assocreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(assocreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(assocreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the Map rule. *)
let rec mapreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((mapreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(mapreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((mapreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(mapreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(mapreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  mapreductionSb subs pr = 
  match pr with
    | [] -> (match subs with 
               | Cp(Pt(e1,s1),s2) -> Pt(Sb(e1,s2),Cp(s1,s2)) 
               | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((mapreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((mapreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(mapreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(mapreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the IdL rule. *)
let rec idlreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((idlreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(idlreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((idlreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(idlreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(idlreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  idlreductionSb subs pr = 
  match pr with
    | [] -> (match subs with 
               | Cp(Id,sb) -> sb 
               | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((idlreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((idlreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(idlreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(idlreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the IdR rule. *)
let rec idrreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((idrreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(idrreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((idrreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(idrreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(idrreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  idrreductionSb subs pr = 
  match pr with
    | [] -> (match subs with 
               | Cp(sb,Id) -> sb 
               | _ -> subs)
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((idrreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((idrreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(idrreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(idrreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the ShiftCons rule. *)
let rec shiftconsreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((shiftconsreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(shiftconsreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((shiftconsreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(shiftconsreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(shiftconsreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  shiftconsreductionSb subs pr = 
  match pr with
    | [] -> (match subs with Cp(Up,Pt(e1,sb)) -> sb | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((shiftconsreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((shiftconsreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(shiftconsreductionSb s2 tail))
                      | Pt(e1,s2)     -> Pt(e1,(shiftconsreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the VarShift rule. *)
let rec varshiftreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((varshiftreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(varshiftreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((varshiftreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(varshiftreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(varshiftreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  varshiftreductionSb subs pr = 
  match pr with
    | []        -> (match subs with 
                      | Pt(One,Up) -> Id 
                      | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((varshiftreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((varshiftreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(varshiftreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(varshiftreductionSb s2 tail)))
    | _ -> subs

(** Implementation of the SCons rule. *)
let rec sconsreduction exp pr = 
  match pr with 
    | [] -> exp
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((sconsreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sconsreduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((sconsreduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(sconsreduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(sconsreductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  sconsreductionSb subs pr = 
  match pr with
    | [] -> (match subs with 
               | Pt(Sb(One,s1),Cp(Up,s2)) -> 
                   if s1=s2 
                   then s1
                   else subs
               | _ -> subs)
    | 1 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((sconsreductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((sconsreduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(sconsreductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(sconsreductionSb s2 tail)))
    | _ -> subs
(* bug found 2004/09/12 - conditional missing in the redex of SCons rule. *)


(** Implementation of the Eta rule. *)
let rec etareduction exp pr = 
  match pr with 
    | [] -> (match exp with 
               | L(A(e1,One),_,_) -> (Sematchls.sbnorm (Sb(e1,Pt(Dummy,Id)))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | A(e1,e2) -> A((etareduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(etareduction e1 tail,variable_name,lambda_type)
                      | Sb(e1,s2) -> Sb((etareduction e1 tail),s2)
                      | _ -> assert false)
    | 2 :: tail -> (match exp with
                      | Dummy -> exp
                      | One -> exp
                      | Vr c -> exp
                      | L(e1,_,_) -> exp
                      | A(e1,e2) -> A(e1,(etareduction e2 tail))
                      | Sb(e1,s2) -> Sb(e1,(etareductionSb s2 tail))
                      | _ -> assert false)
    | _ -> exp
and  
  etareductionSb subs pr = 
  match pr with
    | [] -> Sematchls.sbnormsb(subs)
    | 1 :: tail -> (match subs with  
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp((etareductionSb s1 tail),s2)
                      | Pt(e1,s2) -> Pt((etareduction e1 tail),s2))
    | 2 :: tail -> (match subs with
                      | Id -> subs
                      | Up -> subs
                      | Cp(s1,s2) -> Cp(s1,(etareductionSb s2 tail))
                      | Pt(e1,s2) -> Pt(e1,(etareductionSb s2 tail)))
    | _ -> subs
