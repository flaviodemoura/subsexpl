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

(** This module contains the lexer for the lambda s_e calculus and some functions used for reductions.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Genlex

open Setypes

(* Lexer for the lambda s_e calculus *)
(*-----------------------------------*)

(** This is the lexer: it contains the operators used in lambda s_e expressions. *)
let lexer2 = make_lexer ["L"; "A"; "S"; "P"; "("; ")"; ","]
               
(** This is the parser. *)
let rec  parse_expr2 = parser
  | [< 'Ident s >] -> (Vr s)
  | [< 'Int i >] -> (DB  i)
  | [< 'Kwd "A";  'Kwd "("; e1 = parse_expr2; 'Kwd ","; e2 = parse_expr2; 'Kwd ")" >] -> A(e1,e2)
  | [< 'Kwd "L"; 'Kwd "("; e1 = parse_expr2;  'Kwd ")" >] -> L(e1,"x",BaseType("A")) 
  | [< 'Kwd "S"; 'Kwd "("; 'Int i;  'Kwd ","; e1 = parse_expr2; 'Kwd ","; e2 = parse_expr2; 'Kwd ")" >] -> S(i,e1,e2) 
  | [< 'Kwd "P"; 'Kwd "("; 'Int i;  'Kwd ","; 'Int j; 'Kwd ","; e1 = parse_expr2; 'Kwd ")" >] -> P(i,j,e1) 
      
(** This function converts a string into the corresponding lambda s_e expression in the language used by SUBSEXPL. *)
let convertStr2Exp_lse s = parse_expr2 (lexer2 (Stream.of_string s))
                             
