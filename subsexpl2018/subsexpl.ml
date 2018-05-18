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


(** This is the module that contains the main loop.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Char
open Printf
open Genlex
open Buffer

open Setypes

(* The main procedure *) 
(* ------------------ *) 

let rec main_loop_new () =
  try
    Output.new_menu ();
    let op = Input.get_line () in
      match op with 
        | "0" -> Pure.lpure  main_loop_new (* opcoes anteriores *)
        | "1" -> Pure.lpurecomb  main_loop_new (* opcoes anteriores *)
        | "4" -> 
            Output.lgrammar ();
            main_loop_new ()
        | "5" -> 
            Output.new_grammar ();
            main_loop_new ()
        | "6" -> raise Quit
        | _ -> 
	    print_string "Invalid Input!\n"; 
            main_loop_new ()
  with Quit -> print_string "Good bye!\n"  

 
(** This is the main loop that calls each calculus separately. *)
let rec main_loop () =
  try
    Output.fst_menu ();
    let op = Input.get_line () in
      match op with 
        | "0" -> main_loop_new ()
        | "1" -> Sigma.lsigma main_loop 
        | "2" -> Lambdase.lse main_loop 
        | "3" -> Susp.lsusp main_loop 
        | "4" -> Suspcomb.lsuspcomb main_loop
        | "5" -> 
            Output.lgrammar ();
            main_loop ()
        | "6" -> raise Quit
        | _ -> 
            print_string "Invalid Input!\n"; 
            main_loop ()
    with Quit -> print_string "Good bye!\n" 

(** This is the function that decide if the input comes from the keyboard or from a file. *)    
let _ =
  if Array.length Sys.argv = 2
  then
    let f = open_in Sys.argv.(1) in 
      Input.input_file := Some f;
      main_loop ()
  else
    main_loop ()
      
(***************************Example****************************************)
(* We must include the rules IdR and IdL of the lambda-sigma-calculus     *)
(* without the if conditional. The example follows:                       *)
(* 1[^][Dummy.id] -> 1[^o(Dummy.id)] -> 1[^oid] at this point we need the *)
(* rule to eliminate the composition and get the desired result.          *)
(**************************************************************************)

