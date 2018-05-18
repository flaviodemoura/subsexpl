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

(** this module contains the lexer for the suspension combining calculus and some functions used for reductions. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Genlex

open Setypes

let lexer4 = make_lexer [ "A"; "L"; "Sp"; "Con"; "("; ")"; ","; "Ar"; "Paar"; "Nilen" ]
               
(** The parser for expressions of the suspension combining calculus. *)
let rec  parse_expr4 = parser
  | [< 'Ident s >] -> (Vr s) 
  | [< 'Int i;  >] -> (DB  i)
  | [< 'Kwd "A";  'Kwd "("; e1 = parse_expr4; 'Kwd ","; e2 = parse_expr4; 'Kwd ")" >] -> A(e1,e2)
  | [< 'Kwd "L"; 'Kwd "("; e1 = parse_expr4;  'Kwd ")" >] -> L(e1,"x",BaseType("A")) 
  | [< 'Kwd "Sp"; 'Kwd "("; e1 = parse_expr4; 'Kwd ","; 'Int i; 'Kwd ","; 'Int j; 'Kwd ","; env = parse_env; 'Kwd ")" >] -> Sp(e1,i,j,env) 
and
  parse_env = parser
    | [< 'Kwd "Nilen" >] -> Nilen
    | [< 'Kwd "Con"; 'Kwd "("; envt = parse_envt; 'Kwd ","; env = parse_env; 'Kwd ")" >] -> Con(envt,env)
and 
  parse_envt = parser
    | [< 'Kwd "Ar"; 'Int i; >] -> Ar i
    | [< 'Kwd "Paar";  'Kwd "("; e1 = parse_expr4;  'Kwd ","; 'Int i; 'Kwd ")" >] -> Paar(e1,i)
  
(** Function that converts an expression given by the user to internal language of the suspension combining calculus used in SUBSEXPL. *)
let convertStr2Exp_suscomb s = parse_expr4 (lexer4 (Stream.of_string s))

