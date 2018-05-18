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

(** This module contains the functions that generate the list of redexes for each of the rewriting rules implemented in module {{:Seredls.html}Seredls}
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(* matching checks for the lambda sigma calculus *)
(* --------------------------------------------- *)

(* to be implemented 

let rec matchingBeta1 exp l pos =  
match exp with 
  | Dummy -> l 
  | One -> l 
  | Vr c -> l
  | A(L(e1),e2) -> let c_list = matchingBeta1 e1 (pos::l) (1::1::pos) in
      matchingBeta1 e2 c_list (2::pos)
  | A(e1,e2) -> let c_list = matchingBeta1 e1 l (1::pos) in
      matchingBeta1 e2 c_list (2::pos)
  | L(e1)       -> matchingBeta1 e1 l (1::pos)
  | Sb(e1,sb)   -> let c_list = matchingBeta1 e1 l (1::pos) in
      matchingBetaSb sb c_list (2::pos)
  | _ -> assert false
and
matchingBetaSb subs l pos =  
match subs with 
  | Up -> l
  | Id -> l
  | Pt(e1,sb) -> let c_list = matchingBeta1 e1 l (1::pos) in
      matchingBetaSb sb c_list (2::pos)
  | Cp(s1,s2) -> let c_list = matchingBetaSb s1 l (1::pos) in
      matchingBetaSb s2 c_list (2::pos)

*)

let rec matchingBeta1 exp l pos =  
  match exp with 
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(L(e1,_,_),e2) -> 
        pos :: List.append 
          (matchingBeta1 e1 l (List.append pos [1;1])) 
          (matchingBeta1 e2 [] (List.append pos [2]))
    | A(e1,e2) -> 
        List.append 
          (matchingBeta1 e1 l (List.append pos [1])) 
          (matchingBeta1 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingBeta1 e1 l (List.append pos [1]))
    | Sb(e1,sb) -> 
        List.append 
          (matchingBeta1 e1 l (List.append pos [1])) 
          (matchingBetaSb sb [] (List.append pos [2]))
    | _ -> assert false
and matchingBetaSb subs l pos =  
  match subs with 
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingBeta1 e1 l (List.append pos [1])) 
          (matchingBetaSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingBetaSb s1 l (List.append pos [1])) 
          (matchingBetaSb s2 [] (List.append pos [2]))

let rec matchingApp exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingApp e1 l (List.append pos [1])) 
          (matchingApp e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingApp e1 l (List.append pos [1])
    | Sb(A(e1,e2),sb) -> 
        pos :: List.append 
          (List.append 
             (matchingApp e1 l (List.append pos [1;1]))
             (matchingApp e2 l (List.append pos [1;2])))
          (matchingAppSb sb [] (List.append pos [2]))
    | Sb(e1,sb) ->  
        List.append 
          (matchingApp e1 l (List.append pos [1])) 
          (matchingAppSb sb [] (List.append pos [2]))
    | _ -> assert false
and matchingAppSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingApp e1 l (List.append pos [1])) 
          (matchingAppSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingAppSb s1 l (List.append pos [1])) 
          (matchingAppSb s2 [] (List.append pos [2]))
          
let rec matchingAbs exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingAbs e1 l (List.append pos [1])) 
          (matchingAbs e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingAbs e1 l (List.append pos [1])
    | Sb(L(e1,_,_),sb) -> 
        pos :: List.append 
          (matchingAbs e1 l (List.append pos [1;1]))
          (matchingAbsSb sb [] (List.append pos [2]))
    | Sb(e1,sb) -> 
        List.append 
          (matchingAbs e1 l (List.append pos [1])) 
          (matchingAbsSb sb [] (List.append pos [2]))
    | _ -> assert false
and matchingAbsSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingAbs e1 l (List.append pos [1])) 
          (matchingAbsSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingAbsSb s1 l (List.append pos [1])) 
          (matchingAbsSb s2 [] (List.append pos [2]))

let rec matchingClos exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingClos e1 l (List.append pos [1])) 
          (matchingClos e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingClos e1 l (List.append pos [1])
    | Sb(Sb(e1,s1),s2) -> 
        pos :: List.append 
          (List.append 
             (matchingClos e1 l (List.append pos [1;1]))
             (matchingClosSb s1 l (List.append pos [1;2])))
          (matchingClosSb s2 [] (List.append pos [2]))
    | Sb(e1,sb) ->  
        List.append 
          (matchingClos e1 l (List.append pos [1])) 
          (matchingClosSb sb [] (List.append pos [2]))
    | _ -> assert false
and matchingClosSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingClos e1 l (List.append pos [1])) 
          (matchingClosSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingClosSb s1 l (List.append pos [1])) 
          (matchingClosSb s2 [] (List.append pos [2]))

let rec matchingVarCons exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingVarCons e1 l (List.append pos [1])) 
          (matchingVarCons e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingVarCons e1 l (List.append pos [1])
    | Sb(One,Pt(e1,sb)) -> 
        pos :: List.append 
          (matchingVarCons e1 l (List.append pos [2;1]))
          (matchingVarConsSb sb [] (List.append pos [2;2]))
    | Sb(e1,sb) ->  
        List.append 
          (matchingVarCons e1 l (List.append pos [1])) 
          (matchingVarConsSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingVarConsSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingVarCons e1 l (List.append pos [1])) 
          (matchingVarConsSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingVarConsSb s1 l (List.append pos [1])) 
          (matchingVarConsSb s2 [] (List.append pos [2]))

let rec matchingId exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingId e1 l (List.append pos [1])) 
          (matchingId e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingId e1 l (List.append pos [1])
    | Sb(e1,Id) -> pos :: (matchingId e1 l (List.append pos [1]))
    | Sb(e1,sb) ->  
        List.append 
          (matchingId e1 l (List.append pos [1])) 
          (matchingIdSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingIdSb subs l pos = 
  match subs with
    | Up -> l 
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingId e1 l (List.append pos [1])) 
          (matchingIdSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingIdSb s1 l (List.append pos [1])) 
          (matchingIdSb s2 [] (List.append pos [2]))

let rec matchingAssoc exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingAssoc e1 l (List.append pos [1])) 
          (matchingAssoc e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingAssoc e1 l (List.append pos [1])
    | Sb(e1,sb) -> 
        List.append 
          (matchingAssoc e1 l (List.append pos [1])) 
          (matchingAssocSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingAssocSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingAssoc e1 l (List.append pos [1])) 
          (matchingAssocSb sb [] (List.append pos [2]))
    | Cp(Cp(s1,s2),t) -> 
        pos :: List.append
          (List.append
             (matchingAssocSb s1 l (List.append pos [1;1])) 
             (matchingAssocSb s2 [] (List.append pos [1;2])))
          (matchingAssocSb t [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingAssocSb s1 l (List.append pos [1])) 
          (matchingAssocSb s2 [] (List.append pos [2]))
          
let rec matchingMap exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingMap e1 l (List.append pos [1])) 
          (matchingMap e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingMap e1 l (List.append pos [1])
    | Sb(e1,sb)   ->  
        List.append 
          (matchingMap e1 l (List.append pos [1]))
          (matchingMapSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingMapSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingMap e1 l (List.append pos [1])) 
          (matchingMapSb sb [] (List.append pos [2]))
    | Cp(Pt(e1,s2),t) -> 
        pos :: List.append
          (List.append
             (matchingMap e1 l (List.append pos [1;1])) 
             (matchingMapSb s2 [] (List.append pos [1;2])))
          (matchingMapSb t [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingMapSb s1 l (List.append pos [1]))
          (matchingMapSb s2 [] (List.append pos [2]))

let rec matchingIdL exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingIdL e1 l (List.append pos [1])) 
          (matchingIdL e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingIdL e1 l (List.append pos [1])
    | Sb(e1,sb) ->  
        List.append 
          (matchingIdL e1 l (List.append pos [1])) 
          (matchingIdLSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingIdLSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingIdL e1 l (List.append pos [1])) 
          (matchingIdLSb sb [] (List.append pos [2]))
    | Cp(Id,sb) -> pos :: (matchingIdLSb sb l (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingIdLSb s1 l (List.append pos [1])) 
          (matchingIdLSb s2 [] (List.append pos [2]))

let rec matchingIdR exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingIdR e1 l (List.append pos [1])) 
          (matchingIdR e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingIdR e1 l (List.append pos [1])
    | Sb(e1,sb) -> 
        List.append 
          (matchingIdR e1 l (List.append pos [1])) 
          (matchingIdRSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingIdRSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingIdR e1 l (List.append pos [1])) 
          (matchingIdRSb sb [] (List.append pos [2]))
    | Cp(sb,Id) -> pos :: (matchingIdRSb sb l (List.append pos [1]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingIdRSb s1 l (List.append pos [1])) 
          (matchingIdRSb s2 [] (List.append pos [2]))

let rec matchingShiftCons exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingShiftCons e1 l (List.append pos [1])) 
          (matchingShiftCons e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingShiftCons e1 l (List.append pos [1])
    | Sb(e1,sb) -> 
        List.append 
          (matchingShiftCons e1 l (List.append pos [1])) 
          (matchingShiftConsSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingShiftConsSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingShiftCons e1 l (List.append pos [1])) 
          (matchingShiftConsSb sb [] (List.append pos [2]))
    | Cp(Up,Pt(e1,sb)) -> 
        pos :: List.append
          (matchingShiftCons e1 l (List.append pos [2;1])) 
          (matchingShiftConsSb sb [] (List.append pos [2;2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingShiftConsSb s1 l (List.append pos [1])) 
          (matchingShiftConsSb s2 [] (List.append pos [2]))

let rec matchingVarShift exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingVarShift e1 l (List.append pos [1])) 
          (matchingVarShift e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingVarShift e1 l (List.append pos [1])
    | Sb(e1,sb) ->  
        List.append 
          (matchingVarShift e1 l (List.append pos [1])) 
          (matchingVarShiftSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingVarShiftSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(One,Up) -> pos :: l
    | Pt(e1,sb) -> 
        List.append 
          (matchingVarShift e1 l (List.append pos [1])) 
          (matchingVarShiftSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingVarShiftSb s1 l (List.append pos [1])) 
          (matchingVarShiftSb s2 [] (List.append pos [2]))

let rec matchingSCons exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSCons e1 l (List.append pos [1])) 
          (matchingSCons e2 [] (List.append pos [2]))
    | L(e1,_,_) -> matchingSCons e1 l (List.append pos [1])
    | Sb(e1,sb) ->  
        List.append 
          (matchingSCons e1 l (List.append pos [1])) 
          (matchingSConsSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingSConsSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(Sb(One,s1),Cp(Up,s2)) -> 
        (if (s1 = s2) 
         then 
           (pos :: List.append 
              (matchingSConsSb s1 l (List.append pos [1;2]))  
              (matchingSConsSb s2 [] (List.append pos [2;2]))) 
         else 
           List.append 
             (matchingSConsSb s1 l (List.append pos [1;2]))  
             (matchingSConsSb s2 [] (List.append pos [2;2])))
    | Pt(e1,sb) -> 
        List.append 
          (matchingSCons e1 l (List.append pos [1])) 
          (matchingSConsSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingSConsSb s1 l (List.append pos [1])) 
          (matchingSConsSb s2 [] (List.append pos [2]))

let rec occurdummy1 exp = 
  match exp with
    | Dummy -> true
    | One -> false
    | Vr c -> false
    | A(e1,e2) -> ((occurdummy1 e1) || (occurdummy1 e2))
    | L(e1,_,_) -> (occurdummy1 e1)
    | Sb(e1,sb) -> ((occurdummy1 e1) || (occurdummy1sb sb)) 
    | _ -> assert false 
and occurdummy1sb subs =
  match subs with
    | Pt(e1,sb) -> ((occurdummy1 e1) || (occurdummy1sb sb))
    | Cp(s1,s2) -> ((occurdummy1sb s1) || (occurdummy1sb s2))
    | _ -> false

let rec sbnorm exp = 
  match exp with
    | Dummy -> Dummy
    | One -> One
    | Vr c -> Vr c
    | Sb(A(e1,e2),sb) -> 
        (if (occurdummy1(e1)||occurdummy1(e2)||occurdummy1sb(sb)) 
         then A(sbnorm(Sb(e1,sb)),sbnorm(Sb(e2,sb))) 
         else exp)
    | Sb(L(e1,lambda_variable_name,lambdaType),sb) -> 
        (if (occurdummy1(e1)||occurdummy1sb(sb)) 
         then L(sbnorm(Sb(e1,Pt(One,Cp(sb,Up)))), lambda_variable_name, lambdaType) 
         else exp)
    | Sb(Sb(e1,s1),s2) -> sbnorm(Sb(e1,sbnormsb(Cp(s1,s2))))
    | Sb(One,Pt(e1,sb)) -> 
        (if (occurdummy1(e1) || occurdummy1sb(sb)) 
         then sbnorm(e1) 
         else exp)
    | Sb(e1,Id) -> 
        (if occurdummy1(e1) 
         then sbnorm(e1) 
         else exp)
    | _ -> exp
and sbnormsb subs = 
  match subs with
    | Up -> Up
    | Id -> Id
    | Cp(Id,sb) -> sbnormsb(sb)
    | Cp(sb,Id) -> sbnormsb(sb)
    | Cp(Up,Pt(e1,sb)) -> 
        (if (occurdummy1(e1) || occurdummy1sb(sb)) 
         then sbnormsb(sb) 
         else subs)
    | Cp(Cp(sb1,sb2),sb3) -> 
        (if (occurdummy1sb(sb1)||occurdummy1sb(sb2)||occurdummy1sb(sb3)) 
         then sbnormsb(Cp(sbnormsb(sb1),sbnormsb(Cp(sb2,sb3)))) 
         else subs)
    | Cp(Pt(e1,s1),s2) -> 
        (if (occurdummy1(e1) || occurdummy1sb(s1) || occurdummy1sb(s2)) 
         then sbnormsb(Pt(sbnorm(Sb(e1,s2)),sbnormsb(Cp(s1,s2)))) 
         else subs)
    | Pt(Sb(One,s1),Cp(Up,s2)) -> 
        (if ((s1 = s2)&&(occurdummy1sb(s1))) 
         then sbnormsb(s1) 
         else subs)
    | _ -> subs

(* The inclusion of the rules IdR and IdL without the if *)
(* was necessary because the lambda-sigma-calculus *)
(* include some simbols from pure terms that must  *)
(* be eliminated. See an example at the end of this file.*) 
      
let rec holdsEta exp = (not (occurdummy1 (sbnorm(Sb(exp,Pt(Dummy,Id))))))
                         
let rec matchingEta exp l pos = 
  match exp with
    | Dummy -> l
    | One -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingEta e1 l (List.append pos [1])) 
          (matchingEta e2 [] (List.append pos [2]))
    | L(A(e1,One),_,_) -> 
        (if (holdsEta e1) 
         then pos :: (matchingEta e1 l (List.append pos [1;1])) 
         else (matchingEta e1 l (List.append pos [1;1])))
    | L(e1,_,_) -> matchingEta e1 l (List.append pos [1])
    | Sb(e1,sb) -> 
        List.append 
          (matchingEta e1 l (List.append pos [1])) 
          (matchingEtaSb sb [] (List.append pos [2]))
    | _ -> assert false 
and matchingEtaSb subs l pos = 
  match subs with
    | Up -> l
    | Id -> l
    | Pt(e1,sb) -> 
        List.append 
          (matchingEta e1 l (List.append pos [1])) 
          (matchingEtaSb sb [] (List.append pos [2]))
    | Cp(s1,s2) -> 
        List.append 
          (matchingEtaSb s1 l (List.append pos [1])) 
          (matchingEtaSb s2 [] (List.append pos [2]))
