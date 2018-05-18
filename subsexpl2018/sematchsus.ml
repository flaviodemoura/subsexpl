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

(** This module contains the functions that generate the list of redexes for each of the rewriting rules implemented in module {{:Seredsus.html}Seredsus}
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(* matching checks for the suspension calculus *)
(* ------------------------------------------- *)

let rec matchingBetas exp l pos =
match exp with
  | Dummy -> l
  | DB i -> l
  | Vr c -> l
  | A(L(e1,_,_),e2) -> 
      pos :: List.append 
        (matchingBetas e1 l (List.append pos [1;1]))
        (matchingBetas e2 [] (List.append pos [2]))
  | A(e1,e2) -> 
      List.append 
        (matchingBetas e1 l (List.append pos [1]))
        (matchingBetas e2 [] (List.append pos [2]))
  | L(e1,_,_) -> (matchingBetas e1 l (List.append pos [1]))
  | Sp(e1,_,_,env) -> 
      List.append 
        (matchingBetas e1 l (List.append pos [1]))
        (matchingBetaEnv env [] (List.append pos [2]))
  | _ -> assert false
and  matchingBetaEnv env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingBetaEt envt l (List.append pos [1]))
          (matchingBetaEnv env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingBetaEnv env1 l (List.append pos [1]))
          (matchingBetaEnv env2 [] (List.append pos [2]))
and  matchingBetaEt envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingBetaEt envt1 l (List.append pos [1]))
          (matchingBetaEnv env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matchingBetas e1 l (List.append pos [1]))
        

let rec matching_r1 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r1 e1 l (List.append pos [1]))
          (matching_r1 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r1 e1 l (List.append pos [1]))
    | Sp(Vr c,_,_,env) -> 
        pos :: (matchingEnv_r1 env l (List.append pos [2]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_r1 e1 l (List.append pos [1])) 
          (matchingEnv_r1 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_r1 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_r1 envt l (List.append pos [1]))
          (matchingEnv_r1 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r1 env1 l (List.append pos [1]))
          (matchingEnv_r1 env2 [] (List.append pos [2]))
and matchingEt_r1 envt l pos =
  match envt with
    | Ar i -> l 
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r1 envt1 l (List.append pos [1]))
          (matchingEnv_r1 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r1 e1 l (List.append pos [1]))
        
let rec matching_r2 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r2 e1 l (List.append pos [1]))
          (matching_r2 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r2 e1 l (List.append pos [1]))
    | Sp(DB i,0,_,Nilen) -> pos :: l
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_r2 e1 l (List.append pos [1])) 
          (matchingEnv_r2 env [] (List.append pos [2]))
    | _ -> assert false
and matchingEnv_r2 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_r2 envt l (List.append pos [1]))
          (matchingEnv_r2 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r2 env1 l (List.append pos [1]))
          (matchingEnv_r2 env2 [] (List.append pos [2]))
and matchingEt_r2 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r2 envt1 l (List.append pos [1]))
          (matchingEnv_r2 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r2 e1 l (List.append pos [1]))
        
let rec matching_r3 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r3 e1 l (List.append pos [1])) 
          (matching_r3 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r3 e1 l (List.append pos [1]))
    | Sp(DB 1,_,_,Con(Ar(i),env)) -> 
        pos :: (matchingEnv_r3 env l (List.append pos [2]))
    | Sp(e1,_,_,env) -> 
        List.append (matching_r3 e1 l (List.append pos [1])) 
          (matchingEnv_r3 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_r3 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_r3 envt l (List.append pos [1]))
          (matchingEnv_r3 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r3 env1 l (List.append pos [1]))
          (matchingEnv_r3 env2 [] (List.append pos [2]))
and matchingEt_r3 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r3 envt1 l (List.append pos [1]))
          (matchingEnv_r3 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r3 e1 l (List.append pos [1]))
        
let rec matching_r4 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r4 e1 l (List.append pos [1])) 
          (matching_r4 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r4 e1 l (List.append pos [1]))
    | Sp(DB 1,_,_,Con(Paar(e1,i),env)) -> 
        pos :: List.append 
          (matching_r4 e1 l (List.append pos [2;1;1]))
          (matchingEnv_r4 env [] (List.append pos [2;2]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_r4 e1 l (List.append pos [1]))
          (matchingEnv_r4 env [] (List.append pos [2]))
    | _ -> assert false
and matchingEnv_r4 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_r4 envt l (List.append pos [1]))
          (matchingEnv_r4 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r4 env1 l (List.append pos [1]))
          (matchingEnv_r4 env2 [] (List.append pos [2]))
and matchingEt_r4 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r4 envt1 l (List.append pos [1]))
          (matchingEnv_r4 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> 
        (matching_r4 e1 l (List.append pos [1]))

let rec matching_r5 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r5 e1 l (List.append pos [1]))
          (matching_r5 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r5 e1 l (List.append pos [1]))
    | Sp(DB i,_,_,Con(envt,env)) -> 
        (if i > 1 
         then 
           (pos :: 
              List.append 
              (matchingEt_r5 envt l (List.append pos [2;1]))
              (matchingEnv_r5 env [] (List.append pos [2;2])))
         else (*bug found and corrected Dec 14, 2004.*)
           List.append 
             (matchingEt_r5 envt l (List.append pos [2;1]))
             (matchingEnv_r5 env [] (List.append pos [2;2])))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_r5 e1 l (List.append pos [1])) 
          (matchingEnv_r5 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_r5 env l pos =
  match env with
    | Nilen -> l 
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_r5 envt l (List.append pos [1]))
          (matchingEnv_r5 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r5 env1 l (List.append pos [1]))
          (matchingEnv_r5 env2 [] (List.append pos [2]))
and matchingEt_r5 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r5 envt1 l (List.append pos [1]))
          (matchingEnv_r5 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r5 e1 l (List.append pos [1]))

let rec matching_r6 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l 
    | A(e1,e2) -> 
        List.append 
          (matching_r6 e1 l (List.append pos [1])) 
          (matching_r6 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r6 e1 l (List.append pos [1]))
    | Sp(A(e1,e2),_,_,env) -> 
        pos :: List.append
          (List.append 
             (matching_r6 e1 l (List.append pos [1;1]))
             (matching_r6 e2 [] (List.append pos [1;2])))
          (matchingEnv_r6 env [] (List.append pos [2]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_r6 e1 l (List.append pos [1])) 
          (matchingEnv_r6 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_r6 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_r6 envt l (List.append pos [1]))
          (matchingEnv_r6 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r6 env1 l (List.append pos [1]))
          (matchingEnv_r6 env2 [] (List.append pos [2]))
and matchingEt_r6 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r6 envt1 l (List.append pos [1]))
          (matchingEnv_r6 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r6 e1 l (List.append pos [1]))
        
let rec matching_r7 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_r7 e1 l (List.append pos [1])) 
          (matching_r7 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_r7 e1 l (List.append pos [1]))
    | Sp(L(e1,_,_),_,_,env) -> 
        pos :: List.append 
          (matching_r7 e1 l (List.append pos [1;1]))
          (matchingEnv_r7 env [] (List.append pos [2]))
    | Sp(e1,_,_,env) ->  
        List.append 
          (matching_r7 e1 l (List.append pos [1])) 
          (matchingEnv_r7 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_r7 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_r7 envt l (List.append pos [1]))
          (matchingEnv_r7 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_r7 env1 l (List.append pos [1]))
          (matchingEnv_r7 env2 [] (List.append pos [2]))
and matchingEt_r7 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_r7 envt1 l (List.append pos [1]))
          (matchingEnv_r7 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_r7 e1 l (List.append pos [1]))
        
let rec occurdummy3 exp = 
  match exp with
    | Dummy -> true
    | DB i -> false
    | Vr c -> false
    | A(e1,e2) -> ((occurdummy3 e1) || (occurdummy3 e2))
    | L(e1,_,_) -> (occurdummy3 e1)
    | Sp(e1,_,_,env) -> ((occurdummy3 e1) || (occurdummy3_Env env)) 
    | _ -> assert false
and occurdummy3_Env env =
  match env with
    | Nilen -> false
    | Con(envt,env1) -> ((occurdummy3_Et envt) || (occurdummy3_Env env1))
    | Ck(env1,_,_,env2) -> ((occurdummy3_Env env1) || (occurdummy3_Env env2))
and occurdummy3_Et envt =
  match envt with
    | Ar i -> false
    | LG(envt1,_,_,env1) -> ((occurdummy3_Et envt1) || (occurdummy3_Env env1))
    | Paar(e1,i) -> (occurdummy3 e1)
 
let rec spnorm exp = 
  match exp with
    | Dummy -> Dummy
    | DB i -> DB i
    | Vr c -> Vr c 
    | Sp(Dummy,i,j,env) -> Dummy (* These three rules don't have the IF conditional by the same reason explained at the end of this file for the lambda-sigma calculus *)
    | Sp(DB i,0,j,Nilen) -> DB (i+j)
    | Sp(DB 1,i,j,Con(Ar(k),env)) -> DB (j-k)
    | Sp(DB 1,i,j,Con(Paar(e1,k),env)) -> 
        (if (occurdummy3 e1) then spnorm(Sp(e1,0,j-k,Nilen)) else exp)
    | Sp(DB i,j,k,Con(envt,env)) -> 
        (if ((occurdummy3_Et envt) || (occurdummy3_Env env)) 
         then spnorm(Sp(DB (i-1),j-1,k,env)) 
         else exp)
    | Sp(A(e1,e2),i,j,env) -> 
        (if ((occurdummy3 e1) || (occurdummy3 e2) || (occurdummy3_Env env)) 
         then A(spnorm(Sp(e1,i,j,env)),spnorm(Sp(e2,i,j,env))) 
         else exp) 
    | Sp(L(e1,variable_name,lambda_type),i,j,env) -> 
        (if ((occurdummy3 e1) || (occurdummy3_Env env)) 
         then L(spnorm(Sp(e1,i+1,j+1,Con(Ar(j),env))), variable_name,lambda_type) 
         else exp)
    | _ -> exp
        
let rec holds_Eta exp = 
  (not (occurdummy3 ( spnorm(Sp(exp,1,0,Con(Paar(Dummy,0),Nilen))))))
    
let rec matching_Eta exp l pos = 
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_Eta e1 l (List.append pos [1]))
          (matching_Eta e2 [] (List.append pos [2]))
    | L(A(e1,DB 1),_,_)-> 
        (if (holds_Eta e1) 
         then pos :: (matching_Eta e1 l (List.append pos [1;1])) 
         else (matching_Eta e1 l (List.append pos [1;1])))
    | L(e1,_,_) -> matching_Eta e1 l (List.append pos [1])
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_Eta e1 l (List.append pos [1]))
          (matching_Eta_Env env [] (List.append pos [2]))
    | _ -> assert false
and matching_Eta_Env env l pos = 
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matching_Eta_Et envt l (List.append pos [1]))
          (matching_Eta_Env env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matching_Eta_Env env1 l (List.append pos [1]))
          (matching_Eta_Env env2 [] (List.append pos [2]))
and matching_Eta_Et envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matching_Eta_Et envt1 l (List.append pos [1]))
          (matching_Eta_Env env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_Eta e1 l (List.append pos [1]))
        
let rec matching_m1 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m1 e1 l (List.append pos [1])) 
          (matching_m1 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m1 e1 l (List.append pos [1]))
    | Sp(Sp(e1,_,_,env1),_,_,env2) -> 
        pos :: List.append
          (List.append 
             (matching_m1 e1 l (List.append pos [1;1]))
             (matchingEnv_m1 env1 [] (List.append pos [1;2])))
          (matchingEnv_m1 env2 [] (List.append pos [2]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m1 e1 l (List.append pos [1])) 
          (matchingEnv_m1 env [] (List.append pos [2]))
    | _ -> assert false
and matchingEnv_m1 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_m1 envt l (List.append pos [1]))
          (matchingEnv_m1 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m1 env1 l (List.append pos [1]))
          (matchingEnv_m1 env2 [] (List.append pos [2]))
and matchingEt_m1 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m1 envt1 l (List.append pos [1]))
          (matchingEnv_m1 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m1 e1 l (List.append pos [1]))
        
let rec matching_m2 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m2 e1 l (List.append pos [1])) 
          (matching_m2 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m2 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) ->  
        List.append 
          (matching_m2 e1 l (List.append pos [1])) 
          (matchingEnv_m2 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m2 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_m2 envt l (List.append pos [1]))
          (matchingEnv_m2 env1 [] (List.append pos [2]))
    | Ck(Nilen,_,0,Nilen) -> pos::l
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m2 env1 l (List.append pos [1]))
          (matchingEnv_m2 env2 [] (List.append pos [2]))
and matchingEt_m2 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m2 envt1 l (List.append pos [1]))
          (matchingEnv_m2 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m2 e1 l (List.append pos [1]))
        
let rec matching_m3 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l 
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m3 e1 l (List.append pos [1])) 
          (matching_m3 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m3 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m3 e1 l (List.append pos [1])) 
          (matchingEnv_m3 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m3 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_m3 envt l (List.append pos [1]))
          (matchingEnv_m3 env1 [] (List.append pos [2]))
    | Ck(Nilen,i,j,Con(envt,env1)) -> 
        (if ((i>=1)&&(j>=1)) 
         then (pos:: List.append
                 (matchingEt_m3 envt l (List.append pos [2;1]))
                 (matchingEnv_m3 env1 [] (List.append pos [2;2]))) 
         else (* Bug found and corrected. Dec 14, 2004. *)
           (List.append
              (matchingEt_m3 envt l (List.append pos [2;1]))
              (matchingEnv_m3 env1 [] (List.append pos [2;2])))) 
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m3 env1 l (List.append pos [1]))
          (matchingEnv_m3 env2 [] (List.append pos [2]))
and matchingEt_m3 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m3 envt1 l (List.append pos [1]))
          (matchingEnv_m3 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m3 e1 l (List.append pos [1]))
        
let rec matching_m4 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m4 e1 l (List.append pos [1])) 
          (matching_m4 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m4 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m4 e1 l (List.append pos [1])) 
          (matchingEnv_m4 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m4 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_m4 envt l (List.append pos [1]))
          (matchingEnv_m4 env1 [] (List.append pos [2]))
    | Ck(Nilen,0,j,env) -> 
        pos:: (matchingEnv_m4 env l (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m4 env1 l (List.append pos [1]))
          (matchingEnv_m4 env2 [] (List.append pos [2]))
and matchingEt_m4 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m4 envt1 l (List.append pos [1]))
          (matchingEnv_m4 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m4 e1 l (List.append pos [1]))
        
let rec matching_m5 exp l pos =
  match exp with
    | Dummy -> l 
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) ->
        List.append 
          (matching_m5 e1 l (List.append pos [1])) 
          (matching_m5 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m5 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m5 e1 l (List.append pos [1])) 
          (matchingEnv_m5 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m5 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_m5 envt l (List.append pos [1]))
          (matchingEnv_m5 env1 [] (List.append pos [2]))
    | Ck(Con(envt,env1),i,j,env2) -> 
        pos:: List.append
          (List.append 
             (matchingEt_m5 envt l (List.append pos [1;1]))
             (matchingEnv_m5 env1 [] (List.append pos [1;2])))
          (matchingEnv_m5 env2 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m5 env1 l (List.append pos [1]))
          (matchingEnv_m5 env2 [] (List.append pos [2]))
and matchingEt_m5 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m5 envt1 l (List.append pos [1]))
          (matchingEnv_m5 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m5 e1 l (List.append pos [1]))
        
let rec matching_m6 exp l pos =
  match exp with
    | Dummy -> l 
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m6 e1 l (List.append pos [1])) 
          (matching_m6 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m6 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m6 e1 l (List.append pos [1])) 
          (matchingEnv_m6 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m6 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_m6 envt l (List.append pos [1]))
          (matchingEnv_m6 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m6 env1 l (List.append pos [1]))
          (matchingEnv_m6 env2 [] (List.append pos [2]))
and matchingEt_m6 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,i,0,Nilen) -> pos::(matchingEt_m6 envt1 l (List.append pos [1]))
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m6 envt1 l (List.append pos [1]))
          (matchingEnv_m6 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m6 e1 l (List.append pos [1]))

let rec matching_m7 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m7 e1 l (List.append pos [1])) 
          (matching_m7 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m7 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) ->  
        List.append 
          (matching_m7 e1 l (List.append pos [1])) 
          (matchingEnv_m7 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m7 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_m7 envt l (List.append pos [1]))
          (matchingEnv_m7 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) ->
        List.append 
          (matchingEnv_m7 env1 l (List.append pos [1]))
          (matchingEnv_m7 env2 [] (List.append pos [2]))
and matchingEt_m7 envt l pos =
  match envt with
    | Ar i -> l
    | LG(Ar(m),i,j,Con(Ar(k),env)) -> 
        (if (i=m+1) 
         then (pos::(matchingEnv_m7 env l (List.append pos [2;2]))) 
         else (* Bug found and corrected. Dec 14, 2004.*)
           (matchingEnv_m7 env l (List.append pos [2;2])))
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m7 envt1 l (List.append pos [1]))
          (matchingEnv_m7 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m7 e1 l (List.append pos [1]))

let rec matching_m8 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m8 e1 l (List.append pos [1])) 
          (matching_m8 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m8 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m8 e1 l (List.append pos [1])) 
          (matchingEnv_m8 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m8 env l pos =
  match env with
    | Nilen -> l
    | Con(envt, env1) -> 
        List.append 
          (matchingEt_m8 envt l (List.append pos [1]))
          (matchingEnv_m8 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m8 env1 l (List.append pos [1]))
          (matchingEnv_m8 env2 [] (List.append pos [2]))
and matchingEt_m8 envt l pos =
  match envt with
    | Ar i -> l
    | LG(Ar(m),i,j,Con(Paar(e1,k),env)) -> 
        (if (i=m+1) 
         then (pos::List.append 
                 (matching_m8 e1 l (List.append pos [2;1;1]))
                 (matchingEnv_m8 env [] (List.append pos [2;2]))) 
         else (* Bug found and corrected. Dec 14, 2004.*)
           (List.append 
              (matching_m8 e1 l (List.append pos [2;1;1]))
              (matchingEnv_m8 env [] (List.append pos [2;2]))))
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m8 envt1 l (List.append pos [1]))
          (matchingEnv_m8 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m8 e1 l (List.append pos [1]))

let rec matching_m9 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m9 e1 l (List.append pos [1])) 
          (matching_m9 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> (matching_m9 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env) -> 
        List.append 
          (matching_m9 e1 l (List.append pos [1])) 
          (matchingEnv_m9 env [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m9 env l pos =
  match env with
    | Nilen -> l
    | Con(envt,env1) -> 
        List.append 
          (matchingEt_m9 envt l (List.append pos [1]))
          (matchingEnv_m9 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m9 env1 l (List.append pos [1]))
          (matchingEnv_m9 env2 [] (List.append pos [2]))
and matchingEt_m9 envt l pos =
  match envt with
    | Ar i -> l
    | LG(Paar(e1,k),i,j,Con(envt1,env1)) -> 
        (if (k=i) 
         then  pos :: List.append
           (List.append 
              (matching_m9 e1 l (List.append pos [1;1]))
              (matchingEt_m9 envt1 [] (List.append pos [2;1])))
           (matchingEnv_m9 env1 [] (List.append pos [2;2])) 
         else (*Bug found and corrected. Dec 14, 2004. *)
           (List.append
              (List.append 
                 (matching_m9 e1 l (List.append pos [1;1]))
                 (matchingEt_m9 envt1 [] (List.append pos [2;1])))
              (matchingEnv_m9 env1 [] (List.append pos [2;2]))))
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m9 envt1 l (List.append pos [1]))
          (matchingEnv_m9 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m9 e1 l (List.append pos [1]))

let sbn x y = (if (x-y)>0 then (x-y) else 0)
                
let rec len env =
  match env with
    | Nilen -> 0
    | Con(envt,env1) -> 1 + (len env1)
    | Ck(env1,i,j,env2) -> (len env1)+(sbn (len env2) i) 

let rec ind envt = 
  match envt with
    | Ar k -> k + 1
    | Paar(e1,k) -> k
    | LG(envt1,j,k,env1) -> 
        (if ((len env1)>(sbn j (ind(envt1)))) 
         then ((index (sbn j (ind(envt1))) env1)+(sbn j k)) 
         else ind(envt1))
and idx env = index 0 env
and index m env =
  match env with
    | Nilen -> 0
    | Con(envt1,env1) -> 
        (if (m=0) 
         then (ind envt1) 
         else (index (m-1) env1))
    | Ck(env1,j,k,env2) -> 
        (if (m < (len env1)) 
         then (if (len env2)>(sbn j (index m env1)) 
               then ((index (sbn j (index m env1)) env2)+(sbn j k)) 
               else (index m env1)) 
         else (index (m-(len env1)+j) env2))
          
let rec matching_m10 exp l pos =
  match exp with
    | Dummy -> l
    | DB i -> l
    | Vr c -> l
    | A(e1,e2) -> 
        List.append 
          (matching_m10 e1 l (List.append pos [1])) 
          (matching_m10 e2 [] (List.append pos [2]))
    | L(e1,_,_) -> 
        (matching_m10 e1 l (List.append pos [1]))
    | Sp(e1,_,_,env1) -> 
        List.append 
          (matching_m10 e1 l (List.append pos [1])) 
          (matchingEnv_m10 env1 [] (List.append pos [2])) 
    | _ -> assert false
and matchingEnv_m10 env l pos =
  match env with
    | Nilen -> l
    | Con(envt1, env1) -> 
        List.append 
          (matchingEt_m10 envt1 l (List.append pos [1]))
          (matchingEnv_m10 env1 [] (List.append pos [2]))
    | Ck(env1,_,_,env2) -> 
        List.append 
          (matchingEnv_m10 env1 l (List.append pos [1]))
          (matchingEnv_m10 env2 [] (List.append pos [2]))
and matchingEt_m10 envt l pos =
  match envt with
    | Ar i -> l
    | LG(envt1,i,j,Con(envt2,env1)) -> 
        (if (i <> ind(envt1)) 
         then (pos :: List.append
                 (List.append 
                    (matchingEt_m10 envt1 l (List.append pos [1]))
                    (matchingEt_m10 envt2 [] (List.append pos [2;1])))
                 (matchingEnv_m10 env1 [] (List.append pos [2;2]))) 
         else (* Bug found and corrected. Dec 14, 2004.*)
           (List.append
              (List.append 
                 (matchingEt_m10 envt1 l (List.append pos [1]))
                 (matchingEt_m10 envt2 [] (List.append pos [2;1])))
              (matchingEnv_m10 env1 [] (List.append pos [2;2])))) 
    | LG(envt1,_,_,env1) -> 
        List.append 
          (matchingEt_m10 envt1 l (List.append pos [1]))
          (matchingEnv_m10 env1 [] (List.append pos [2]))
    | Paar(e1,i) -> (matching_m10 e1 l (List.append pos [1]))

