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

(** This module contains some functions used for simulating the pure lambda calculus via the lambda s_e calculus of explicit substitutions.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)

open Setypes
open Sematchlse
open Seredlse
open Sematchsuscomb
open Seredsuscomb

(** This function takes an expression exp as argument and generates a
    list of pairs of the form (rule name, positions where this rule
    apply). *)
let lst_pure exp = 
  [("Beta: ",(matchingBeta2 exp [] []));
   ("Eta: ",(matchingETA exp [] []));
   ("Leftmost/outermost normalisation.",[]);
   ("Rightmost/innermost normalisation.",[])
  ]
    
(** This is the normalisation function for the pure lambda calculus
    implemented with the leftmost/outermost strategy. For a given
    expression this function applies one step of beta reduction at the
    leftmost redex and returns the new reduced expression. Note that it
    simulates one step of beta reduction via the lambda s_e calculus
    considering just the initial and the final expressions, that is, it
    hides the intermediate steps. *)
let left_normal_lse expinit pos = 
  let exp = ref (Seredlse.betareduction2 expinit pos) in 
  let posit = ref ([]:int list) in
    while (Lambdase.left_red_lse !exp []) <> ([],0) do
      posit := Pervasives.fst(Lambdase.left_red_lse !exp []);
      exp :=  (match Pervasives.snd(Lambdase.left_red_lse !exp []) with
                 | 2 -> Seredlse.sltransition !exp !posit
                 | 3 -> Seredlse.satransition !exp !posit
                 | 4 -> Seredlse.sdtransition !exp !posit
                 | 5 -> Seredlse.pltransition !exp !posit
                 | 6 -> Seredlse.patransition !exp !posit
                 | 7 -> Seredlse.pdtransition !exp !posit
                 | 8 -> Seredlse.sstransition !exp !posit
                 | 9 -> Seredlse.sptransition1 !exp !posit
                 | 10 -> Seredlse.sptransition2 !exp !posit
                 | 11 -> Seredlse.pstransition !exp !posit
                 | 12 -> Seredlse.pptransition1 !exp !posit
                 | 13 -> Seredlse.pptransition2 !exp !posit
                 | _ -> assert false)
    done;
    !exp

(** [reduce_pure] takes as argument a lambda expression [ex], an
    interger [rule_number], an integer list [position] and a list of
    4-uples and return a new list of 4-uples which contains a new 4-uple
    formed by the expression [ex] reduced by the rule corresponding to
    [rule_number] at position [position]. *)
let reduce_pure ex rule_number position l_upl =
  match rule_number with 
    | 1 -> (((left_normal_lse ex position),rule_number,position,"\\beta") :: l_upl)
    | 2 -> (((Seredlse.etatransition ex position),rule_number,position,"\\eta") :: l_upl)
    | _ -> assert false 
        
(** This is a normalisation function that uses a leftmost-outermost
    strategy. It takes a list, whose elements are of the form
    (expression,rule_number,position,rule_name), as argument and return a
    list of the same type. *)
let beta_normout l_upl = 
  let new_l_upl = ref l_upl in 
  let exp = ref (Common.first(List.hd !new_l_upl)) in 
    while (Common.pos_leftBR !exp <> [3]) do 
      new_l_upl := reduce_pure !exp 1 (Common.pos_leftBR !exp) !new_l_upl;
      exp := (left_normal_lse !exp (Common.pos_leftBR !exp))
    done; 
    !new_l_upl
      
(** This is a normalisation function that uses a rightmost-innermost
strategy. It takes a list, whose elements are of the form
(expression,rule_number,position,rule_name), as argument and return a
list of the same type. *)
let beta_normin l_upl = 
  let new_l_upl = ref l_upl in 
  let exp = ref (Common.first(List.hd !new_l_upl)) in 
    while (Common.pos_rightBR !exp <> [3]) do 
      new_l_upl := reduce_pure !exp 1 (Common.pos_rightBR !exp) !new_l_upl;
      exp := (left_normal_lse !exp (Common.pos_rightBR !exp))
    done; 
    !new_l_upl

(*********** using the suspension calculus ***********)

(** This function takes an expression exp as argument and generates a
    list of pairs of the form (rule name, positions where this rule
    apply). *)
let lst_purecomb exp = 
  [("Beta: ",(matchingBetascomb exp [] []));
   ("Eta: ",(matching_Etascomb exp [] []));
   ("Leftmost/outermost normalisation.",[]);
   ("Rightmost/innermost normalisation.",[])
  ]

(** This is the normalisation function for the pure lambda calculus
    implemented with the leftmost/outermost strategy. For a given
    expression this function applies one step of beta reduction at the
    leftmost redex and returns the new reduced expression. Note that it
    simulates one step of beta reduction via the lambda s_e calculus
    considering just the initial and the final expressions, that is, it
    hides the intermediate steps. *)
let left_normal_susp expinit pos = 
  let exp = ref (Seredsuscomb.betasreductioncomb expinit pos) in 
  let posit = ref ([]:int list) in
    while (Suspcomb.left_red_suscomb !exp []) <> ([],0) do
      posit := Pervasives.fst(Suspcomb.left_red_suscomb !exp []);
      exp :=  (match Pervasives.snd(Suspcomb.left_red_suscomb !exp []) with
                 | 3 -> Seredsuscomb.r1_combreduction !exp !posit
                 | 4 -> Seredsuscomb.r2_combreduction !exp !posit
                 | 5 -> Seredsuscomb.r3_combreduction !exp !posit
                 | 6 -> Seredsuscomb.r4_combreduction !exp !posit
                 | 7 -> Seredsuscomb.r5_combreduction !exp !posit
                 | 8 -> Seredsuscomb.r6_combreduction !exp !posit
                 | 9 -> Seredsuscomb.r7_combreduction !exp !posit
                 | 10 -> Seredsuscomb.r8_combreduction !exp !posit
                 | 11 -> Seredsuscomb.r9_combreduction !exp !posit
                 | 12 -> Seredsuscomb.r10_combreduction !exp !posit
                 | 13 -> Seredsuscomb.r11_combreduction !exp !posit
                 | _ -> assert false)
    done;
    !exp

(** [reduce_pure] takes as argument a lambda expression [ex], an
    interger [rule_number], an integer list [position] and a list of
    4-uples and return a new list of 4-uples which contains a new 4-uple
    formed by the expression [ex] reduced by the rule corresponding to
    [rule_number] at position [position]. *)
let reduce_purecomb ex rule_number position l_upl =
  match rule_number with 
    | 1 -> (((left_normal_susp ex position),rule_number,position,"\\beta") :: l_upl)
    | 2 -> (((Seredsuscomb.eta_combreduction ex position),rule_number,position,"\\eta") :: l_upl)
    | _ -> assert false 
        
(** This is a normalisation function that uses a leftmost-outermost
    strategy. It takes a list, whose elements are of the form
    (expression,rule_number,position,rule_name), as argument and return a
    list of the same type. *)
let beta_normoutcomb l_upl = 
  let new_l_upl = ref l_upl in 
  let exp = ref (Common.first(List.hd !new_l_upl)) in 
    while (Common.pos_leftBR !exp <> [3]) do 
      new_l_upl := reduce_purecomb !exp 1 (Common.pos_leftBR !exp) !new_l_upl;
      exp := (left_normal_susp !exp (Common.pos_leftBR !exp))
    done; 
    !new_l_upl
      
(** This is a normalisation function that uses a rightmost-innermost
strategy. It takes a list, whose elements are of the form
(expression,rule_number,position,rule_name), as argument and return a
list of the same type. *)
let beta_normincomb l_upl = 
  let new_l_upl = ref l_upl in 
  let exp = ref (Common.first(List.hd !new_l_upl)) in 
    while (Common.pos_rightBR !exp <> [3]) do 
      new_l_upl := reduce_purecomb !exp 1 (Common.pos_rightBR !exp) !new_l_upl;
      exp := (left_normal_susp !exp (Common.pos_rightBR !exp))
    done; 
    !new_l_upl

