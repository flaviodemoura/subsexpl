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

(** This module contains the implementation of the rewriting rules of the suspension calculus
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(** Implementation of the betas rule. *)
let rec betasreduction exp pr = 
  match pr with 
    | [] -> (match exp with
               | A(L(e1,_,_),e2) -> Sp(e1,1,0,Con(Paar(e2,0),Nilen)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((betasreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(betasreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((betasreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(betasreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(betasreductionEnv env tail)) 
                      | _ -> exp)
    | _ -> exp
and  
  betasreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((betasreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((betasreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(betasreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(betasreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  betasreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((betasreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((betasreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(betasreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r1. *)
let rec r1_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(Vr c,i,j,env) -> Vr c 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r1_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r1_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r1_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r1_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r1_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r1_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r1_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r1_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r1_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r1_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  r1_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r1_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r1_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r1_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r2. *)
let rec r2_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,0,j,Nilen) -> DB (i+j) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r2_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r2_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r2_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r2_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r2_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r2_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r2_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r2_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r2_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r2_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r2_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r2_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r2_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r2_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r3. *)
let rec r3_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB 1,i,j,Con(Ar(k),env)) -> DB (j-k)
               | _ -> exp )
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r3_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r3_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r3_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r3_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r3_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r3_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r3_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r3_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r3_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r3_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r3_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r3_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r3_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r3_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r4. *)
let rec r4_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB 1,i,j,Con(Paar(e1,k),env)) -> Sp(e1,0,(j-k),Nilen) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r4_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r4_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r4_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r4_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r4_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r4_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r4_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r4_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r4_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r4_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r4_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r4_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r4_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r4_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r5. *)
let rec r5_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,j,k,Con(envt,env)) -> Sp(DB (i-1),(j-1),k,env) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r5_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r5_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env)-> Sp((r5_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r5_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r5_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r5_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r5_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r5_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r5_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r5_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r5_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r5_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r5_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r5_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r6. *)        
let rec r6_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(A(e1,e2),i,j,env) -> A(Sp(e1,i,j,env),Sp(e2,i,j,env)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r6_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r6_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r6_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r6_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r6_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp 
and  
  r6_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r6_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r6_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r6_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r6_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  r6_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r6_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r6_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r6_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r7. *)
let rec r7_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(L(e1,variable_name,lambda_type),i,j,env) -> L(Sp(e1,i+1,j+1,Con(Ar(j),env)),variable_name,lambda_type)
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r7_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r7_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r7_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r7_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r7_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r7_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r7_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r7_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r7_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r7_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r7_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r7_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r7_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r7_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the eta rule. *)
let rec eta_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | L(A(e1,DB 1),_,_) -> Sematchsus.spnorm (Sp(e1,1,0,Con(Paar(Dummy,0),Nilen))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((eta_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(eta_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((eta_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(eta_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(eta_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  eta_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1)    -> Con((eta_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((eta_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(eta_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(eta_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  eta_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with  
                      | Paar(e1,i) -> Paar((eta_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((eta_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(eta_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** implementation of the rule m1. *)
let rec m1_reduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(Sp(e1,i1,j1,env1),i2,j2,env2) -> Sp(e1,i1+(Sematchsus.sbn i2 j1),j2+(Sematchsus.sbn j1 i2),Ck(env1,j1,i2,env2)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m1_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m1_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m1_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m1_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m1_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m1_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m1_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m1_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m1_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m1_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m1_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m1_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m1_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m1_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m2. *)
let rec m2_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m2_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m2_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m2_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m2_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m2_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m2_reductionEnv env pr = 
  match pr with
    | [] -> (match env with 
               | Ck(Nilen,_,0,Nilen) -> Nilen 
               | _ -> env)
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m2_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m2_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m2_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m2_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m2_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with  
                      | Paar(e1,i)   -> Paar((m2_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m2_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m2_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m3. *)
let rec m3_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m3_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m3_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m3_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m3_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m3_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m3_reductionEnv env pr = 
  match pr with
    | [] -> (match env with 
               | Ck(Nilen,i,j,Con(envt,env1)) -> Ck(Nilen,i-1,j-1,env1) 
               | _ -> env)
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m3_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m3_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m3_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m3_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m3_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m3_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m3_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m3_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m4. *)
let rec m4_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with   
	              | A(e1,e2) -> A((m4_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m4_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m4_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m4_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m4_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m4_reductionEnv env pr = 
  match pr with
    | [] -> (match env with 
               | Ck(Nilen,0,j,env) -> env 
               | _ -> env)
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m4_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m4_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m4_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m4_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m4_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m4_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m4_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m4_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m5. *)
let rec m5_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m5_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m5_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m5_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m5_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m5_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m5_reductionEnv env pr = 
  match pr with
    | [] -> (match env with 
               | Ck(Con(envt,env1),i,j,env2) -> Con(LG(envt,i,j,env2),Ck(env1,i,j,env2)) 
               | _ -> env)
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m5_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m5_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m5_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m5_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m5_reductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i)   -> Paar((m5_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m5_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m5_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m6. *)
let rec m6_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m6_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m6_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m6_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m6_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m6_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m6_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m6_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m6_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m6_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m6_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  m6_reductionEt envt pr = 
  match pr with 
    | [] -> (match envt with 
               | LG(envt1,i,0,Nilen) -> envt1 
               | _ -> envt)
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m6_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m6_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m6_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m7. *)
let rec m7_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m7_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m7_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m7_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m7_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m7_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m7_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m7_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m7_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m7_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m7_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m7_reductionEt envt pr = 
  match pr with 
    | [] -> (match envt with 
               | LG(Ar m,i,j,Con(Ar k,env)) -> Ar(k+(Sematchsus.sbn i j)) 
               | _ -> envt)
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m7_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m7_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m7_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m8. *)
let rec m8_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with   
	              | A(e1,e2) -> A((m8_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m8_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m8_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m8_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m8_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m8_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m8_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m8_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m8_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m8_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m8_reductionEt envt pr = 
  match pr with 
    | [] -> (match envt with 
               | LG(Ar m,i,j,Con(Paar(e1,k),env)) -> Paar(e1,k+(Sematchsus.sbn i j)) 
               | _ -> envt)
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m8_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m8_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m8_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r9. *)
let rec m9_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m9_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m9_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env)  -> Sp((m9_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m9_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m9_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m9_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m9_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m9_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m9_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m9_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m9_reductionEt envt pr = 
  match pr with 
    | [] -> (match envt with 
               | LG(Paar(e1,k),i,j,Con(envt1,env1)) -> Paar(Sp(e1,j,Sematchsus.ind(envt1),Con(envt1,env1)),Sematchsus.ind(envt1)+(Sematchsus.sbn i j)) 
               | _ -> envt)
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m9_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m9_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m9_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule m10. *)
let rec m10_reduction exp pr =
  match pr with
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((m10_reduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(m10_reduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((m10_reduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(m10_reduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(m10_reductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  m10_reductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((m10_reductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((m10_reductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(m10_reductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(m10_reductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  m10_reductionEt envt pr = 
  match pr with 
    | [] -> (match envt with 
               | LG(envt1,i,j,Con(envt2,env1)) -> LG(envt1,i-1,j-1,env1) 
               | _ -> envt) 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((m10_reduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((m10_reductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(m10_reductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt
