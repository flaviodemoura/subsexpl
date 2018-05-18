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

(** This module contains the functions that generate the list of redexes for each of the rewriting rules implemented in module {{:Seredlse.html}Seredlse}
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(***********************************************)
(* Matching checks for the lambda s_e calculus *)
(*---------------------------------------------*)


let rec matchingBeta2 exp l pos =  
  match exp with 
    | Dummy -> l
    | DB i -> l 
    | Vr c -> l
    | A(L(e1,_,_),e2) -> 
        pos :: List.append 
          (matchingBeta2 e1 l (List.append pos [1;1]))
          (matchingBeta2 e2 [] (List.append pos [2]))
    | A(e1,e2) -> 
        List.append 
          (matchingBeta2 e1 l (List.append pos [1]))
          (matchingBeta2 e2 [] (List.append pos [2])) 
    | L(e1,_,_) -> (matchingBeta2 e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingBeta2 e1 l (List.append pos [1]))
          (matchingBeta2 e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingBeta2 e1 l (List.append pos [1]))
    | _ -> assert false

let rec matchingSLtransition exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSLtransition e1 l (List.append pos [1]))
          (matchingSLtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSLtransition e1 l (List.append pos [1]))
    | S(i,L(e1,_,_),e2) -> 
        pos :: List.append 
          (matchingSLtransition e1 l (List.append pos [1;1]))
          (matchingSLtransition e2 [] (List.append pos [2]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingSLtransition e1 l (List.append pos [1]))
          (matchingSLtransition e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSLtransition e1 l (List.append pos [1]))
    | _ -> assert false

let rec matchingSAtransition exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSAtransition e1 l (List.append pos [1]))
          (matchingSAtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSAtransition e1 l (List.append pos [1]))
    | S(i,A(e1,e2),e3) -> 
        pos :: List.append 
          (List.append 
             (matchingSAtransition e1 l (List.append pos [1;1]))
             (matchingSAtransition e2 [] (List.append pos [1;2])))
          (matchingSAtransition e3 [] (List.append pos [2]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingSAtransition e1 l (List.append pos [1]))
          (matchingSAtransition e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSAtransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingSDtransition exp l pos = 
  match exp with 
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSDtransition e1 l (List.append pos [1]))
          (matchingSDtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSDtransition e1 l (List.append pos [1]))
    | S(i, DB j,e1) -> pos :: (matchingSDtransition e1 l (List.append pos [2]))
    | S(i,e1,e2)    -> 
        List.append 
          (matchingSDtransition e1 l (List.append pos [1]))
          (matchingSDtransition e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSDtransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPLtransition exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingPLtransition e1 l (List.append pos [1]))
          (matchingPLtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingPLtransition e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingPLtransition e1 l (List.append pos [1]))
          (matchingPLtransition e2 [] (List.append pos [2]))
    | P(j,k,L(e1,_,_)) -> pos :: (matchingPLtransition e1 l (List.append pos [1;1]))
    | P(j,k,e1) -> (matchingPLtransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPAtransition exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingPAtransition e1 l (List.append pos [1]))
          (matchingPAtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingPAtransition e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingPAtransition e1 l (List.append pos [1]))
          (matchingPAtransition e2 [] (List.append pos [2]))
    | P(j,k,A(e1,e2)) -> 
        pos :: List.append 
          (matchingPAtransition e1 l (List.append pos [1;1]))
          (matchingPAtransition e2 [] (List.append pos [1;2]))
    | P(j,k,e1) -> (matchingPAtransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPDtransition exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingPDtransition e1 l (List.append pos [1]))
          (matchingPDtransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingPDtransition e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingPDtransition e1 l (List.append pos [1]))
          (matchingPDtransition e2 [] (List.append pos [2])) 
    | P(j,k,DB i) -> pos :: l
    | P(j,k,e1) -> (matchingPDtransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingSStransition exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSStransition e1 l (List.append pos [1]))
          (matchingSStransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSStransition e1 l (List.append pos [1]))
    | S(j,S(i,e1,e2),e3) -> 
	(if i <= j 
	 then (pos :: List.append 
                 (matchingSStransition (S(i,e1,e2)) l (List.append pos [1]))
                 (matchingSStransition e3 [] (List.append pos [2]))) 
	 else (List.append 
                 (matchingSStransition (S(i,e1,e2)) l (List.append pos [1]))
                 (matchingSStransition e3 [] (List.append pos [2]))))
          (* Bug found and corrected 20/03/2003 *)
    | S(i,e1,e2) -> 
        List.append 
          (matchingSStransition e1 l (List.append pos [1]))
          (matchingSStransition e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSStransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingSPtransition1 exp l pos = 
  match exp with 
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSPtransition1 e1 l (List.append pos [1]))
          (matchingSPtransition1 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSPtransition1 e1 l (List.append pos [1]))
    | S(j,P(i,k,e1),e2) -> 
	(if k<j && j<k+i 
	 then (pos :: List.append 
                 (matchingSPtransition1 e1 l (List.append pos [1;1]))
                 (matchingSPtransition1 e2 [] (List.append pos [2])))
         else (List.append 
                 (matchingSPtransition1 e1 l (List.append pos [1;1]))
                 (matchingSPtransition1 e2 [] (List.append pos [2]))))
    | S(i,e1,e2) -> 
        List.append 
          (matchingSPtransition1 e1 l (List.append pos [1]))
          (matchingSPtransition1 e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSPtransition1 e1 l (List.append pos [1]))
    | _ -> assert false

let rec matchingSPtransition2 exp l pos = 
  match exp with 
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingSPtransition2 e1 l (List.append pos [1]))
          (matchingSPtransition2 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingSPtransition2 e1 l (List.append pos [1]))
    | S(j,P(i,k,e1),e2) -> 
	(if k+i<=j 
	 then (pos :: List.append 
                 (matchingSPtransition2 e1 l (List.append pos [1;1]))
                 (matchingSPtransition2 e2 [] (List.append pos [2])))
         else (List.append 
                 (matchingSPtransition2 e1 l (List.append pos [1;1]))
                 (matchingSPtransition2 e2 [] (List.append pos [2])))) 
    | S(i,e1,e2) -> 
        List.append 
          (matchingSPtransition2 e1 l (List.append pos [1]))
          (matchingSPtransition2 e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingSPtransition2 e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPStransition exp l pos = 
  match exp with 
    | Dummy -> l
    | DB i -> l 
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingPStransition e1 l (List.append pos [1]))
          (matchingPStransition e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingPStransition e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingPStransition e1 l (List.append pos [1]))
          (matchingPStransition e2 [] (List.append pos [2]))
    | P(i,k,S(j,e1,e2)) -> 
        (if j<=k+1 
	 then (pos :: List.append 
                 (matchingPStransition e1 l (List.append pos [1;1]))
                 (matchingPStransition e2 l (List.append pos [1;2])))
         else (List.append 
                 (matchingPStransition e1 l (List.append pos [1;1]))
                 (matchingPStransition e2 [] (List.append pos [1;2]))))
    | P(j,k,e1) -> (matchingPStransition e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPPtransition1 exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingPPtransition1 e1 l (List.append pos [1]))
          (matchingPPtransition1 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matchingPPtransition1 e1 l (List.append pos [1])) 
    | S(i,e1,e2) -> 
        List.append 
          (matchingPPtransition1 e1 l (List.append pos [1]))
          (matchingPPtransition1 e2 [] (List.append pos [2])) 
    | P(i,k,P(j,m,e1)) -> 
	(if m+j<=k 
	 then (pos :: (matchingPPtransition1 (P(j,m,e1)) l (List.append pos [1])))
         else (matchingPPtransition1  (P(j,m,e1)) l (List.append pos [1])))
	  (* Bug found and corrected 20/03/2003 *)
    | P(j,k,e1) -> (matchingPPtransition1 e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec matchingPPtransition2 exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l 
    | Vr c -> l 
    | A(e1,e2) -> 
        List.append 
          (matchingPPtransition2 e1 l (List.append pos [1]))
          (matchingPPtransition2 e2 [] (List.append pos [2])) 
    | L(e1,_,_) -> (matchingPPtransition2 e1 l (List.append pos [1])) 
    | S(i,e1,e2) -> 
        List.append 
          (matchingPPtransition2 e1 l (List.append pos [1]))
          (matchingPPtransition2 e2 [] (List.append pos [2])) 
    | P(i,k,P(j,m,e1)) -> 
	(if m<=k && k<m+j 
	 then (pos :: (matchingPPtransition2 (P(j,m,e1)) l (List.append pos [1])))
         else (matchingPPtransition2 (P(j,m,e1)) l (List.append pos [1])))
	  (* Bug found and corrected 20/03/2003 *)
    | P(j,k,e1) -> (matchingPPtransition2 e1 l (List.append pos [1]))
    | _ -> assert false
        
let rec occurdummy2 exp =
  match exp with 
    | Dummy -> true
    | DB i -> false
    | Vr c -> false
    | A(e1,e2) -> ((occurdummy2 e1) || (occurdummy2 e2))
    | L(e1,_,_) -> (occurdummy2 e1)
    | S(i,e1,e2) -> ((occurdummy2 e1) || (occurdummy2 e2)) 
    | P(i,k,e1) -> (occurdummy2 e1)
    | _ -> assert false
        
let rec signorm exp =
  match exp with 
    | Dummy -> Dummy
    | DB i -> DB i
    | Vr c -> Vr c  
    | S(i,Vr c,Dummy) -> exp 
    | S(i,DB j,Dummy) -> 
        (if j<i 
         then DB j 
         else (if j>i 
               then (DB (j-1)) 
               else P(0,i,Dummy)))
    | S(i,A(e1,e2),Dummy) -> 
        A((signorm (S(i,e1,Dummy))),(signorm (S(i,e2,Dummy))))
    | S(i,L(e1,variable_name,lambda_type),Dummy) -> L(signorm (S(i+1,e1,Dummy)),variable_name,lambda_type)
    | S(i,S(j,e1,e2),Dummy) -> 
        (if i >= j  
	 then S(j, (signorm (S(i+1,e1,Dummy))),(signorm (S(i-j+1,e2,Dummy))))
         else exp)
    | S(i,P(k,n,e),Dummy) -> 
        (if i>=k+n 
         then P(k,n,(signorm (S(i-n+1,e,Dummy))))
         else (if i>k 
               then P(k,n-1,e) 
               else exp))
    | _ -> exp
        
let holdsEtaCond exp = 
  (not (occurdummy2 (signorm(S(1,exp,Dummy)))))
    
let rec matchingETA exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matchingETA e1 l (List.append pos [1]))
          (matchingETA e2 [] (List.append pos [2]))
    | L(A(e1,DB 1),_,_) -> 
        (if (holdsEtaCond e1) 
         then pos :: (matchingETA e1 l (List.append pos [1;1])) 
         else   (matchingETA e1 l (List.append pos [1;1]))) 
    | L(e1,_,_) -> (matchingETA e1 l (List.append pos [1]))
    | S(i,e1,e2) -> 
        List.append 
          (matchingETA e1 l (List.append pos [1]))
          (matchingETA e2 [] (List.append pos [2]))
    | P(j,k,e1) -> (matchingETA e1 l (List.append pos [1]))
    | _ -> assert false
        
        
