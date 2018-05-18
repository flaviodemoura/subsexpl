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

(** this module contains the lexer for the suspension calculus and some functions used for reductions. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Genlex

open Setypes

let lexer3 = make_lexer [ "A"; "L"; "Sp"; "Con"; "Ck"; "("; ")"; ","; "Ar"; "Paar"; "LG"; "Nilen" ]
               
(** The parser for expressions of the suspension calculus. *)
let rec  parse_expr3 = parser
  | [< 'Ident s >] -> (Vr s) 
  | [< 'Int i;  >] -> (DB  i)
  | [< 'Kwd "A";  'Kwd "("; e1 = parse_expr3; 'Kwd ","; e2 = parse_expr3; 'Kwd ")" >] -> A(e1,e2)
  | [< 'Kwd "L"; 'Kwd "("; e1 = parse_expr3;  'Kwd ")" >] -> L(e1,"x",BaseType("A")) 
  | [< 'Kwd "Sp"; 'Kwd "("; e1 = parse_expr3; 'Kwd ","; 'Int i; 'Kwd ","; 'Int j; 'Kwd ","; env = parse_env; 'Kwd ")" >] -> Sp(e1,i,j,env) 
and
  parse_env = parser
    | [< 'Kwd "Nilen" >] -> Nilen
    | [< 'Kwd "Con"; 'Kwd "("; envt = parse_envt; 'Kwd ","; env = parse_env; 'Kwd ")" >] -> Con(envt,env)
    | [< 'Kwd "Ck"; 'Kwd "("; env1 = parse_env ;  'Kwd ","; 'Int i; 'Kwd ","; 'Int j; 'Kwd ","; env2 = parse_env; 'Kwd ")" >] -> Ck(env1,i,j,env2)
and 
  parse_envt = parser
    | [< 'Kwd "Ar"; 'Int i; >] -> Ar i
    | [< 'Kwd "Paar";  'Kwd "("; e1 = parse_expr3;  'Kwd ","; 'Int i; 'Kwd ")" >] -> Paar(e1,i)
    | [< 'Kwd "LG"; 'Kwd "("; envt1 = parse_envt ;  'Kwd ","; 'Int i; 'Kwd ","; 'Int j; 'Kwd ","; env2 = parse_env; 'Kwd ")" >] -> LG(envt1,i,j,env2)

(** Function that converts an expression given by the user to internal language of the suspension calculus used in SUBSEXPL. *)
let convertStr2Exp_sus s = parse_expr3 (lexer3 (Stream.of_string s))

