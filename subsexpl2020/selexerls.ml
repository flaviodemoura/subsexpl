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

(** this module contains the lexer for the lambda sigma calculus and some functions used for reductions. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Genlex

open Setypes

(* Lexer for the lambda-sigma calculus *)
(*_____________________________________*)

(** This function an auxiliary function used by the convertN function. *)
let rec comp n = 
    match n with
      | 1 -> (Up)
      | n -> (Cp(Up,comp(n-1)))

(** This function converts an integer to the internal codification of de Bruijn indexes used in the lambda sigma calculus. *)
let convertN n = 
    match n with
      | 1 -> One
      | n -> Sb(One,comp(n-1))

(** This i sthe lexer: it contains the operators used in the lambda sigma expressions. *)
let lexer1 = make_lexer [ "A"; "L"; "Sb"; "Pt"; "Cp"; "("; ")"; ","; "Up"; "Id"; "One" ]

(** This is the parser. *)
let rec  parse_expr1 = parser
  | [< 'Ident s >] -> (Vr s) 
  | [< 'Int 1 >] -> (One) 
  | [< 'Int n >] -> (convertN(n))
  | [< 'Kwd "One" >] -> (One)
  | [< 'Kwd "A";  'Kwd "("; e1 = parse_expr1; 'Kwd ","; e2 = parse_expr1; 'Kwd ")" >] -> A(e1,e2)
  | [< 'Kwd "L"; 'Kwd "("; e1 = parse_expr1;  'Kwd ")" >] -> L(e1,"x",BaseType("A")) 
  | [< 'Kwd "Sb"; 'Kwd "("; e1 = parse_expr1 ;  'Kwd ","; sb = parse_subs; 'Kwd ")" >] -> Sb(e1,sb) 
and
  parse_subs = parser
    | [< 'Kwd "Id" >] -> (Id)
    | [< 'Kwd "Up" >] -> (Up)
    | [< 'Kwd "Pt"; 'Kwd "("; e1 = parse_expr1 ;  'Kwd ","; sb = parse_subs; 'Kwd ")" >] -> Pt(e1,sb)
    | [< 'Kwd "Cp"; 'Kwd "("; s1 = parse_subs ;  'Kwd ","; s2 = parse_subs ; 'Kwd ")" >] -> Cp(s1,s2) 

(** This function converts a string into the corresponding lambda sigma expression in the language used by SUBSEXPL. *)
let convertStr2Exp_ls s = parse_expr1 (lexer1 (Stream.of_string s))

