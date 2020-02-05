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

(** This module contains common functions used by all calculi.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(** These are selection functions used in several parts of the
    system. *)
let first  trp = match trp with x,_,_,_ -> x
let secnd  trp = match trp with _,x,_,_ -> x
let third  trp = match trp with _,_,x,_ -> x
let fourth trp = match trp with _,_,_,x -> x

(** This function returns the leftmost beta redex of the given
    expression. This implementation assumes that the given expression is a
    pure lambda term, i.e., a term containing only applications,
    abstractions and de Bruijn indexes. The extension of this function to
    terms containing internal operators of the implemented calculi is easy
    and should be included in a further version of the system. *)
let rec pos_leftBR exp = 
  match (posLeftMostBR exp) with
    | None -> [3]
    | Some p -> p
and
    posLeftMostBR exp = 
  match exp with
    | L(e1,_,_) -> 
        (match posLeftMostBR e1 with
           | None -> None
           | Some p -> Some (1::p))
    | A(e1,e2) -> 
        (match e1 with
           | L(ex,_,_) -> Some []
           | _ ->
               match posLeftMostBR e1 with
                 | Some p -> Some (1::p)
                 | None ->
                     match posLeftMostBR e2 with
                       | Some p -> Some (2::p)
                       | None -> None)
    | _ -> None
        
(** This function returns the rightmost beta redex of the given
expression. This implementation assumes that the given expression is a
pure lambda term, i.e., a term containing only applications,
abstractions and de Bruijn indexes. The extension of this function to
terms containing internal operators of the implemented calculi is easy
and should be included in a further version of the system. *)
let rec pos_rightBR exp = 
  match posRightMostBR exp with 
    | None -> [3]
    | Some p -> p
and
  posRightMostBR exp = 
  match exp with
    | L(e1,_,_) -> 
        (match posRightMostBR e1 with
           | None -> None
           | Some p -> Some (1::p))
    | A(e1,e2) -> 
        (match posRightMostBR e2 with
           | Some p -> Some (2::p)
           | None ->
               (match e1 with
                  | L(ex,_,_) -> 
                      (match posRightMostBR ex with
                         | Some p -> Some (1::1::p)
                         | None -> Some [])
                  | _ -> 
                      (match posRightMostBR e1 with
                         | None -> None
                         | Some p -> Some (1::p))))
    | _ -> None
        
