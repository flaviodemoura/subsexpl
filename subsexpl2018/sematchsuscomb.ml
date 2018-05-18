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

(** This module contains the functions that generate the list of redexes for each of the rewriting rules implemented in module {{:Seredsus.html}Seredsuscomb}
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open List

open Setypes

(* matching checks for the suspension combining calculus *)
(* ------------------------------------------- *)

let isPaar et =
match et with
Paar(_,_) -> true |
_ -> false;;

let isAr et =
match et with
Ar(_) -> true |
_ -> false;;

let isSusp t =
match t with
Sp(_,_,_,_) -> true |
_ -> false;;

let indofPaar et =
match et with
Paar(_,l) -> l ;;

let termofPaar et =
match et with
Paar(t,_) -> t ;;

let indofAr et =
match et with
Ar(l) -> l ;;

let termo1suspofPaar et =
match et with
Paar(Sp(v,_,_,_),_) -> v ;;

let termo2suspofPaar et =
match et with
Paar(Sp(_,u,_,_),_) -> u ;;

let termo3suspofPaar et =
match et with
Paar(Sp(_,_,q,_),_) -> q ;;

let termo4suspofPaar et =
match et with
Paar(Sp(_,_,_,z),_) -> z ;;


let rec matchingBetascomb exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(L(e1,_,_),e2)     -> pos :: append (matchingBetascomb e1 l (append pos [1;1]))
                                        (matchingBetascomb e2 [] (append pos [2])) |
       A(e1,e2)    -> append (matchingBetascomb e1 l (append pos [1])) 
                             (matchingBetascomb e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matchingBetascomb e1 l (append pos [1])) |
       Sp(e1,_,_,env)   -> append (matchingBetascomb e1 l (append pos [1]))
                                  (matchingBetaEnvcomb env [] (append pos [2]))
  | _ -> assert false
and  matchingBetaEnvcomb env l pos =
      match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingBetaEtcomb envt l (append pos [1]))
                                   (matchingBetaEnvcomb env1 [] (append pos [2]))
  | _ -> assert false 
and  matchingBetaEtcomb envt l pos =
      match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matchingBetascomb e1 l (append pos [1]))
   | _ -> assert false;;   

let rec matchingBetascombL exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(L(Sp(e1,i,j,Con(Ar(k),env)),_,_),e2)  -> (if ((i >= 1) && (j >= 1)) then 
                   ( pos :: ( append (matchingBetascombL e1 l (append pos [1;1;1])) 
                              (append (matchingBetaEnvcombL env [] (append pos [1;1;2;2])) 
                                      (matchingBetascombL e2 [] (append pos [2]))))) 
                    else
                      ( append (matchingBetascombL e1 l (append pos [1;1;1])) 
                          (append (matchingBetaEnvcombL env [] (append pos [1;1;2;2])) 
                                  (matchingBetascombL e2 [] (append pos [2])))))  |
       A(e1,e2) ->  (append (matchingBetascombL e1 l (append pos [1])) 
                             (matchingBetascombL e2 [] (append pos [2]))) |
       L(e1,_,_)       -> (matchingBetascombL e1 l (append pos [1])) |
       Sp(e1,_,_,env)   -> append (matchingBetascombL e1 l (append pos [1]))
                                  (matchingBetaEnvcombL env [] (append pos [2]))
  | _ -> assert false
and  matchingBetaEnvcombL env l pos =
      match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingBetaEtcombL envt l (append pos [1]))
                                   (matchingBetaEnvcombL env1 [] (append pos [2])) 
  | _ -> assert false 
and  matchingBetaEtcombL envt l pos =
      match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matchingBetascombL e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr1 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr1 e1 l (append pos [1])) 
                             (matching_combr1 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr1 e1 l (append pos [1])) |
       Sp(Vr c,_,_,env)   -> pos :: (matchingEnv_combr1 env l (append pos [2])) |
       Sp(e1,_,_,env)   ->  append (matching_combr1 e1 l (append pos [1])) 
                                   (matchingEnv_combr1 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr1 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr1 envt l (append pos [1]))
                                   (matchingEnv_combr1 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr1 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr1 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr2 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr2 e1 l (append pos [1])) 
                             (matching_combr2 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr2 e1 l (append pos [1])) |
       Sp(Vr c,_,_,env)   -> pos :: (matchingEnv_combr2 env l (append pos [2]))  |
       Sp(e1,_,_,env)   ->  append (matching_combr2 e1 l (append pos [1])) 
                                   (matchingEnv_combr2 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr2 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr2 envt l (append pos [1]))
                                   (matchingEnv_combr2 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr2 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr2 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr3 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr3 e1 l (append pos [1])) 
                             (matching_combr3 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr3 e1 l (append pos [1])) |
       Sp(DB i,j,k,env)   -> (if ( i > j ) then pos :: (matchingEnv_combr3 env l (append pos [2])) else (matchingEnv_combr3 env l (append pos [2]))) |
       Sp(e1,_,_,env)   ->  append (matching_combr3 e1 l (append pos [1])) 
                                   (matchingEnv_combr3 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr3 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr3 envt l (append pos [1]))
                                   (matchingEnv_combr3 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr3 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr3 e1 l (append pos [1]))
  | _ -> assert false 
;;   


let rec select env indx =
match env with
Con(et,envl)  -> if indx = 1 then et 
                  else (select envl (indx -1));;


let rec matching_combr4 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr4 e1 l (append pos [1])) 
                             (matching_combr4 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr4 e1 l (append pos [1])) |
       Sp(DB i,j,_,env)   -> (if (i <= j) && (isAr (select env i) ) then pos :: (matchingEnv_combr4 env l (append pos [2]))
                                                        else (matchingEnv_combr4 env l (append pos [2]))) |
       Sp(e1,_,_,env)   ->  append (matching_combr4 e1 l (append pos [1])) 
                                   (matchingEnv_combr4 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr4 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr4 envt l (append pos [1]))
                                   (matchingEnv_combr4 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr4 envt l pos =
     match envt with
        Ar i ->  l | 
        Paar(e1,i)        -> (matching_combr4 e1 l (append pos [1]))
  | _ -> assert false 
;;   



let rec matching_combr5 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr5 e1 l (append pos [1])) 
                             (matching_combr5 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr5 e1 l (append pos [1])) |
       Sp(DB i,j,_,env)   -> (if (i<=j) && (isPaar (select env i) ) then pos :: (matchingEnv_combr5 env l (append pos [2]))
                                                        else (matchingEnv_combr5 env l (append pos [2]))) |
       Sp(e1,_,_,env)   ->  append (matching_combr5 e1 l (append pos [1])) 
                                   (matchingEnv_combr5 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr5 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr5 envt l (append pos [1]))
                                   (matchingEnv_combr5 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr5 envt l pos =
     match envt with
        Ar i ->  l | 
        Paar(e1,i)        -> (matching_combr5 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr6 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr6 e1 l (append pos [1])) 
                             (matching_combr6 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr6 e1 l (append pos [1])) |
       Sp(A(e1,e2),_,_,env)   -> pos :: append(append (matching_combr6 e1 l (append pos [1;1]))
                                               (matching_combr6 e2 [] (append pos [1;2])))
                                              (matchingEnv_combr6 env [] (append pos [2])) |
       Sp(e1,_,_,env)   ->  append (matching_combr6 e1 l (append pos [1])) 
                                   (matchingEnv_combr6 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr6 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr6 envt l (append pos [1]))
                                   (matchingEnv_combr6 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr6 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr6 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr7 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr7 e1 l (append pos [1])) 
                             (matching_combr7 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr7 e1 l (append pos [1])) |
       Sp(L(e1,_,_),_,_,env)   -> pos :: append (matching_combr7 e1 l (append pos [1;1]))
                                            (matchingEnv_combr7 env [] (append pos [2])) |
       Sp(e1,_,_,env)   ->  append (matching_combr7 e1 l (append pos [1])) 
                                   (matchingEnv_combr7 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr7 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr7 envt l (append pos [1]))
                                   (matchingEnv_combr7 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr7 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr7 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr8 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr8 e1 l (append pos [1])) 
                             (matching_combr8 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr8 e1 l (append pos [1])) |
       Sp(Sp(e1,i,j,env),0,_,Nilen)   -> pos :: (matching_combr8 (Sp(e1,i,j,env)) l (append pos [1])) |
       Sp(e1,_,_,env)   ->  append (matching_combr8 e1 l (append pos [1])) 
                                   (matchingEnv_combr8 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr8 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr8 envt l (append pos [1]))
                                   (matchingEnv_combr8 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr8 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr8 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr9 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr9 e1 l (append pos [1])) 
                             (matching_combr9 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr9 e1 l (append pos [1])) |
       Sp(e1,0,0,Nilen)   -> pos :: (matching_combr9 e1 l (append pos [1])) |
       Sp(e1,_,_,env)   ->  append (matching_combr9 e1 l (append pos [1])) 
                                   (matchingEnv_combr9 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr9 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr9 envt l (append pos [1]))
                                   (matchingEnv_combr9 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr9 envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_combr9 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr10 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr10 e1 l (append pos [1])) 
                             (matching_combr10 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr10 e1 l (append pos [1])) |
       Sp(DB i,j,k,env)   -> (if (i<=j) && (isPaar (select env i)) && (k=(indofPaar (select env i))) 
                              then (pos :: (matchingEnv_combr10 env l (append pos [2])))
                              else (matchingEnv_combr10 env l (append pos [2]))) |
       Sp(e1,_,_,env)   ->  append (matching_combr10 e1 l (append pos [1])) 
                                   (matchingEnv_combr10 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr10 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr10 envt l (append pos [1]))
                                   (matchingEnv_combr10 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr10 envt l pos =
     match envt with
        Ar i ->  l | 
        Paar(e1,i)        -> (matching_combr10 e1 l (append pos [1]))
  | _ -> assert false 
;;   

let rec matching_combr11 exp l pos =
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_combr11 e1 l (append pos [1])) 
                             (matching_combr11 e2 [] (append pos [2])) |
       L(e1,_,_)       -> (matching_combr11 e1 l (append pos [1])) |
       Sp(DB i,j,k,env)   -> (if ((i<=j) && (isPaar (select env i)) && (isSusp (termofPaar (select env i))) && (k<>(indofPaar (select env i)))) 
                              then (pos :: (matchingEnv_combr11 env l (append pos [2])))
                              else (matchingEnv_combr11 env l (append pos [2]))) |
       Sp(e1,_,_,env)   ->  append (matching_combr11 e1 l (append pos [1])) 
                                   (matchingEnv_combr11 env [] (append pos [2])) 
  | _ -> assert false
and matchingEnv_combr11 env l pos =
     match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matchingEt_combr11 envt l (append pos [1]))
                                   (matchingEnv_combr11 env1 [] (append pos [2])) 
  | _ -> assert false 
and matchingEt_combr11 envt l pos =
     match envt with
        Ar i ->  l | 
        Paar(e1,i)        -> (matching_combr11 e1 l (append pos [1]))
  | _ -> assert false 
;;   


let rec occurdummy4 exp = 
match exp with
       Dummy -> true |
       DB i  -> false |
       Vr c  -> false |
       A(e1,e2) -> ((occurdummy4 e1) || (occurdummy4 e2)) |
       L(e1,_,_) -> (occurdummy4 e1) |
       Sp(e1,_,_,env)   -> ((occurdummy4 e1) || (occurdummy4_Env env)) 
  | _ -> assert false
and occurdummy4_Env env =
     match env with
       Nilen             -> false |
       Con(envt,env1)   -> ((occurdummy4_Et envt) || (occurdummy4_Env env1)) 
  | _ -> assert false 
and occurdummy4_Et envt =
     match envt with
        Ar i ->  false |
        Paar(e1,i)        -> (occurdummy4 e1)
  | _ -> assert false 
;;   
 
let rec spcombnorm exp = 
match exp with
       Dummy  -> Dummy |
       DB i   -> DB i |
       Vr c   -> Vr c |        
       Sp(Dummy,i,j,env) -> Dummy |  (* These three rules don't have the IF conditional by the same reason explained at the end of this file for the lambda-sigma calculus *)
       Sp(DB i,0,j,Nilen) -> DB (i+j) |
       Sp(DB 1,i,j,Con(Ar(k),env)) -> DB (j-k) |
       Sp(DB 1,i,j,Con(Paar(e1,k),env)) -> (if (occurdummy4 e1) then spcombnorm(Sp(e1,0,j-k,Nilen)) else exp) |
       Sp(DB i,j,k,Con(envt,env)) -> (if ((occurdummy4_Et envt) || (occurdummy4_Env env)) then spcombnorm(Sp(DB (i-1),j-1,k,env)) else exp) |
       Sp(A(e1,e2),i,j,env) -> (if ((occurdummy4 e1) || (occurdummy4 e2) || (occurdummy4_Env env)) then A(spcombnorm(Sp(e1,i,j,env)),spcombnorm(Sp(e2,i,j,env))) else exp) |
       Sp(L(e1,variable_name,lambda_type),i,j,env) -> (if ((occurdummy4 e1) || (occurdummy4_Env env)) then L(spcombnorm(Sp(e1,i+1,j+1,Con(Ar(j),env))),variable_name,lambda_type) else exp) |
       _ -> exp;;
       
let rec holds_Etascomb exp = 
        (not (occurdummy4 ( spcombnorm(Sp(exp,1,0,Con(Paar(Dummy,0),Nilen))))));;

let rec matching_Etascomb exp l pos = 
match exp with
       Dummy       -> l |
       DB i        -> l |
       Vr c        -> l |
       A(e1,e2)    -> append (matching_Etascomb e1 l (append pos [1])) 
                             (matching_Etascomb e2 [] (append pos [2])) |
       L(A(e1,DB 1),_,_)-> (if (holds_Etascomb e1) then 
                      pos :: (matching_Etascomb e1 l (append pos [1;1])) 
                      else (matching_Etascomb e1 l (append pos [1;1]))) |
       L(e1,_,_)       -> matching_Etascomb e1 l (append pos [1]) |
       Sp(e1,_,_,env)   ->  append (matching_Etascomb e1 l (append pos [1])) 
                              (matching_Etascomb_Env env [] (append pos [2]))
  | _ -> assert false
and 
matching_Etascomb_Env env l pos = 
match env with
       Nilen             -> l |
       Con(envt, env1)   -> append (matching_Etascomb_Et envt l (append pos [1]))
                                   (matching_Etascomb_Env env1 [] (append pos [2])) 
  | _ -> assert false 
and matching_Etascomb_Et envt l pos =
     match envt with
        Ar i ->  l |
        Paar(e1,i)        -> (matching_Etascomb e1 l (append pos [1]))
  | _ -> assert false 
;;   

