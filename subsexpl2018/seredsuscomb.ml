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
open Sematchsuscomb

(** Implementation of the beta_s rule. *)
let rec betasreductioncomb exp pr = 
  match pr with 
    | [] -> (match exp with
               | A(L(e1,_,_),e2) -> Sp(e1,1,0,Con(Paar(e2,0),Nilen)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((betasreductioncomb e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(betasreductioncomb e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((betasreductioncomb e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(betasreductioncomb e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(betasreductioncomEnv env tail)) 
                      | _ -> exp)
    | _ -> exp
and  
  betasreductioncomEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((betasreductioncomEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((betasreductioncomEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(betasreductioncomEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(betasreductioncomEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  betasreductioncomEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((betasreductioncomb e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((betasreductioncomEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(betasreductioncomEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the betasL rule. *)
let rec betaLsreductioncomb exp pr = 
  match pr with 
    | [] -> (match exp with
               | A(L(Sp(e1,i,j,Con(Ar(k),env)),_,_),e2) -> (if ((k + 1) = j) then Sp(e1,i,k,Con(Paar(e2,k),env))
                                                        else exp)  
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((betaLsreductioncomb e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(betaLsreductioncomb e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((betaLsreductioncomb e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(betaLsreductioncomb e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(betaLsreductioncomEnv env tail)) 
                      | _ -> exp)
    | _ -> exp
and  
  betaLsreductioncomEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((betaLsreductioncomEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((betaLsreductioncomEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(betaLsreductioncomEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(betaLsreductioncomEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  betaLsreductioncomEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((betaLsreductioncomb e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((betaLsreductioncomEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(betaLsreductioncomEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r1. *)
let rec r1_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(Vr c,i,j,env) -> Vr c 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r1_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r1_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r1_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r1_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r1_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r1_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r1_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r1_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r1_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r1_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  r1_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r1_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r1_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r1_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r2. *)
let rec r2_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(Vr c,i,j,env) -> Vr c 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r2_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r2_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r2_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r2_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r2_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r2_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r2_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r2_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r2_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r2_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  r2_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r2_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r2_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r2_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt


(** Implementation of the rule r3. *)
let rec r3_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,j,k,env) -> (if (i>j) then DB (i-j+k) else exp)  
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r3_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r3_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r3_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r3_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r3_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r3_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r3_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r3_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r3_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r3_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r3_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r3_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r3_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r3_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt




(** Implementation of the rule r4. *)
let rec r4_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,j,k,env) -> (if ((i<=j) && (isAr (select env i)))  then (DB (k-(indofAr (select env i)))) 
                                      else exp)
               | _ -> exp )
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r4_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r4_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r4_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r4_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r4_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r4_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r4_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r4_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r4_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r4_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r4_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r4_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r4_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r4_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt





(** Implementation of the rule r5. *)
let rec r5_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,j,k,env) -> (if ((i<=j) && (isPaar (select env i))) then Sp( (termofPaar (select env i)),0, k - (indofPaar (select env i)) , Nilen)
                                      else exp) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r5_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r5_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r5_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r5_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r5_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r5_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r5_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r5_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r5_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r5_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r5_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r5_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r5_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r5_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt


(** Implementation of the rule r6. *)        
let rec r6_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(A(e1,e2),i,j,env) -> A(Sp(e1,i,j,env),Sp(e2,i,j,env)) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r6_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r6_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r6_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r6_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r6_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp 
and  
  r6_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r6_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r6_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r6_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r6_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env 
and  
  r6_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r6_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r6_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r6_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r7. *)
let rec r7_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(L(e1,variable_name,lambda_type),i,j,env) -> L(Sp(e1,i+1,j+1,Con(Ar(j),env)),variable_name,lambda_type)
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r7_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r7_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r7_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r7_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r7_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r7_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r7_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r7_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r7_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r7_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r7_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r7_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r7_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r7_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt



(** Implementation of the rule r8. *)
let rec r8_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(Sp(e1,j,k,env),0,kl,Nilen) -> Sp(e1,j,k+kl,env) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r8_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r8_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env)-> Sp((r8_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r8_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r8_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r8_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r8_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r8_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r8_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r8_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r8_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r8_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r8_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r8_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r9. *)
let rec r9_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(e1,0,0,Nilen) -> e1 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r9_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r9_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env)-> Sp((r9_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r9_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r9_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r9_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r9_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r9_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r9_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r9_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r9_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r9_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r9_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r9_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r10. *)
let rec r10_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | Sp(DB i,j,k,env) -> (if ((i<=j) && (isPaar (select env i)) && (k=(indofPaar (select env i)))) then (termofPaar (select env i))
                                      else exp) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r10_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r10_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r10_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r10_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r10_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r10_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r10_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r10_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r10_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r10_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r10_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r10_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r10_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r10_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

(** Implementation of the rule r11. *)
let rec r11_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
(**               | Sp(DB i,j,k,env) -> (if ((i<=j) && (isPaar (select env i)) && (isSusp (termofPaar (select env i))) && (k<>(indofPaar (select env i))))
                                      then  Sp( (termo1suspofPaar (select env i)),(termo2suspofPaar(select env i)),
                                                (termo3suspofPaar(select env i) + k -(indofPaar (select env i))),
                                                (termo4suspofPaar (select env i)))
                                      else exp) 
               | _ -> exp) **)
               | Sp(DB i,j,k,env) -> (if (i<=j) then  
                                       let et = (select env i) in 
                                       (if ((isPaar et) && (isSusp (termofPaar et)) && ( k<>(indofPaar et))) 
                                         then  Sp( (termo1suspofPaar et),(termo2suspofPaar et),
                                                (termo3suspofPaar et + k -(indofPaar et)),
                                                (termo4suspofPaar et))
                                        else exp)
                                        else exp)
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((r11_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(r11_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((r11_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(r11_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(r11_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  r11_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1) -> Con((r11_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((r11_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(r11_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(r11_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  r11_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with
                      | Paar(e1,i) -> Paar((r11_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((r11_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(r11_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt


(** Implementation of the eta rule. *)
let rec eta_combreduction exp pr =
  match pr with
    | [] -> (match exp with 
               | L(A(e1,DB 1),_,_) -> Sematchsus.spnorm (Sp(e1,1,0,Con(Paar(Dummy,0),Nilen))) 
               | _ -> exp)
    | 1 :: tail -> (match exp with
                      | A(e1,e2) -> A((eta_combreduction e1 tail),e2)
                      | L(e1,variable_name,lambda_type) -> L(eta_combreduction e1 tail,variable_name,lambda_type)
                      | Sp(e1,i,j,env) -> Sp((eta_combreduction e1 tail),i,j,env)
                      | _ -> exp)
    | 2 :: tail -> (match exp with
                      | A(e1,e2) -> A(e1,(eta_combreduction e2 tail))
                      | Sp(e1,i,j,env) -> Sp(e1,i,j,(eta_combreductionEnv env tail))
                      | _ -> exp)
    | _ -> exp
and  
  eta_combreductionEnv env pr = 
  match pr with
    | 1 :: tail -> (match env with
                      | Con(envt,env1)    -> Con((eta_combreductionEt envt tail),env1)
                      | Ck(env1,i,j,env2) -> Ck((eta_combreductionEnv env1 tail),i,j,env2)
                      | _ -> env)
    | 2 :: tail -> (match env with
                      | Con(envt,env1) -> Con(envt,(eta_combreductionEnv env1 tail))
                      | Ck(env1,i,j,env2) -> Ck(env1,i,j,(eta_combreductionEnv env2 tail))
                      | _ -> env)
    | _ -> env
and  
  eta_combreductionEt envt pr = 
  match pr with 
    | 1 :: tail -> (match envt with  
                      | Paar(e1,i) -> Paar((eta_combreduction e1 tail),i)
                      | LG(envt1,i,j,env1) -> LG((eta_combreductionEt envt1 tail),i,j,env1)
                      | _ -> envt)
    | 2 :: tail -> (match envt with
                      | LG(envt1,i,j,env1) -> LG(envt1,i,j,(eta_combreductionEnv env1 tail))
                      | _ -> envt)
    | _ -> envt

