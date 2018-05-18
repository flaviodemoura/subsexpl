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

(** This module contains the implementation of the rewriting rules of the lambda s_e calculus
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(** Implementation of the sigma-generation rule. *)
let rec betareduction2 exp pr = 
  match pr with 
    | [] -> (match exp with 
               | A(L(e1,_,_),e2) -> S(1,e1,e2) 
               | _ -> exp)
    | 1 :: tail -> (match exp with 
                      | A(e1,e2) -> A((betareduction2 e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(betareduction2 e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(betareduction2 e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(betareduction2 e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(betareduction2 e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(betareduction2 e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-lambda transition. *)
let rec sltransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | S(i,L(e1,variable_name,lambda_type),e2) -> L(S(i+1,e1,e2),variable_name,lambda_type) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((sltransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sltransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(sltransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(sltransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(sltransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(sltransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-app-transition. *)      
let rec satransition exp pr = 
  match pr with 
    | [] -> (match exp with  
               | S(i,A(e1,e2),e3) -> A(S(i,e1,e3),S(i,e2,e3)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((satransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(satransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(satransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(satransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(satransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(satransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-destruction-transition. *)
let rec sdtransition exp pr =        
  match pr with
    | [] -> (match exp with 
               | S(i,DB n, e1) -> (if n = i 
                                   then P(i,0,e1) 
                                   else (if n > i 
                                         then (DB (n-1)) 
                                         else (DB n))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((sdtransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sdtransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(sdtransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(sdtransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(sdtransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(sdtransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-lambda-transition. *)
let rec pltransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,j,L(e1,variable_name,lambda_type)) -> L(P(i,j+1,e1),variable_name,lambda_type) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((pltransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(pltransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(pltransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(pltransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(pltransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(pltransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-app-transition. *)
let rec patransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,j,A(e1,e2)) -> A(P(i,j,e1),P(i,j,e2)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((patransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(patransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(patransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(patransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(patransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(patransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-desrtuction. *)
let rec pdtransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,k, DB n) -> (if n>k 
                                  then (DB (n+i-1)) 
                                  else (DB n)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((pdtransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(pdtransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(pdtransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(pdtransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(pdtransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(pdtransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-sigma-transition. *)
let rec sstransition exp pr = 
  match pr with           
    | [] -> (match exp with 
               | S(j,S(i,e1,e2),e3) -> (S(i,S(j+1,e1,e3),S(j-i+1,e2,e3))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((sstransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sstransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(sstransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(sstransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(sstransition e2 tail))
                      | S(i,e1,e2)    -> S(i,e1,(sstransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-phi-transition 1. *)
let rec sptransition1 exp pr = 
  match pr with                        
    | [] -> (match exp with 
               | S(j,P(i,k,e1),e2) -> P(i-1,k,e1) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((sptransition1 e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sptransition1 e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(sptransition1 e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(sptransition1 e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(sptransition1 e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(sptransition1 e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the sigma-phi-transition 2. *)
let rec sptransition2 exp pr = 
  match pr with
    | [] -> (match exp with 
               | S(j,P(i,k,e1),e2) -> P(i,k,S(j-i+1,e1,e2)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((sptransition2 e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(sptransition2 e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(sptransition2 e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(sptransition2 e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(sptransition2 e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(sptransition2 e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-sigma-transition. *)
let rec pstransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,k,S(j,e1,e2)) -> S(j,P(i,k+1,e1),P(i,k+1-j,e2)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((pstransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(pstransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(pstransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(pstransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(pstransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(pstransition e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-phi-transition 1. *)
let rec pptransition1 exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,k,P(j,m,e1)) -> P(j,m,P(i,k+1-j,e1)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((pptransition1 e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(pptransition1 e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(pptransition1 e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(pptransition1 e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(pptransition1 e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(pptransition1 e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the phi-phi-transition 2. *)
let rec pptransition2 exp pr = 
  match pr with
    | [] -> (match exp with 
               | P(i,k,P(j,m,e1)) -> P(j+i-1,m,e1) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((pptransition2 e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(pptransition2 e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(pptransition2 e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(pptransition2 e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(pptransition2 e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(pptransition2 e2 tail))
                      | _ -> exp)
    | _ -> exp

(** Implementation of the Eta rule. *)
let rec etatransition exp pr = 
  match pr with
    | [] -> (match exp with 
               | L(A(e1,DB 1),_,_) -> (Sematchlse.signorm (S(1,e1,Dummy))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((etatransition e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(etatransition e1 tail,variable_name,lambda_type)
                      | S(i,e1,e2) -> S(i,(etatransition e1 tail),e2)
                      | P(j,k,e1) -> P(j,k,(etatransition e1 tail))
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(etatransition e2 tail))
                      | S(i,e1,e2) -> S(i,e1,(etatransition e2 tail))
                      | _ -> exp)
    | _ -> exp
