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

(** This module contains the type definitions and the exceptions used in SUBSEXPL. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

(** the string_lexer type. *)
type string_lexer = { string:string; mutable current: int; size:int }


(** The simple type: it's a structure to hold simple types canonically *)
type simpleType = 
    | BaseType of string 
    | FunctionType of simpleType * simpleType

(** The exlambda type: it defines the type for the expressions in the
    pure lambda calculus, in the lambda sigma calculus, in the lambda s_e
    calculus and in the suspension calculus. *)
type exlambda = 
  | L of exlambda * string * simpleType
  | A of exlambda * exlambda
  | DB of int
  | One
  | Vr of string
  | Sb of exlambda * substitution 
  | S of int * exlambda * exlambda
  | P of int * int * exlambda
  | Dummy
  | Sp of exlambda * int * int * environment
  | TermAlias of string
      (** Substitutions used in the lambda sigma calculus. *)
and substitution = 
  | Id
  | Up
  | Pt of exlambda * substitution
  | Cp of substitution * substitution   
(** Environment terms of the suspension calculus. *)
and env_term = 
  | Paar of  exlambda * int
  | Ar of int
  | LG of env_term * int * int * environment      
(** Environments of the suspension calculus. *)
and environment = 
  | Con of env_term * environment
  | Ck of environment * int * int * environment
  | Nilen


(** exception for invalid input *)
exception InvalidInput

(** exception for invalid expressions *)
exception LexerError

(** exception for finishing SUBSEXPL *)
exception Quit

