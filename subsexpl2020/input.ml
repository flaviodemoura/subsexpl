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

(** This module contains all the input functions: functions that ask information - such as a position into a term, a number of a rule - that may come from tha keyboard or from a file. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes

(** input_file is a reference to None or Some f according if the input is given by the keyboard or by a file f, respectively. *)
let input_file = ref None

(** display: will be used to avoid screen scrooling when the input is a file. In the current implementation this option is not work, but it will probably be included in a future version of the system. *)
let display = (!input_file = None)  

(** Read a string from the keyboard or from a file according to the value of input_file. *)
let get_line () = 
  match !input_file with
    | None -> read_line ()
    | Some f ->
	try input_line f
	with 
	  | End_of_file ->
	      input_file := None;
	      read_line ()

(** Convert a string into an integer list. It is used in the ask_pos function below. *)
let convertPos s = 
  if ((s.[0]= '0')&&(String.length s=1)) then [] else
  begin
    let lp = ref [] in
    for i = 0 to ((String.length s)-1) do
      match s.[i] with
      | '1' -> (lp:= 1::!lp)
      | '2' -> (lp:=2::!lp)
      | _ -> raise InvalidInput
    done; List.rev !lp
  end

(** Ask for a position into a term. This position must belong to the given list l_pos. *)
let rec ask_pos l_pos = 
  print_string "Position > ";
  let pos = get_line () in 
    try 
      let position = convertPos pos in
	if (List.mem position l_pos) then position else 
	  begin 
	    print_string "Invalid Position!\n";ask_pos l_pos
	  end 
    with
      | _ -> print_string "Invalid Position!\n"; ask_pos l_pos

(** Ask for an integer - used in the internal loops. This integer is used in the selection of the rules. *)
let rec ask_num() = 
  print_string "Give the number: ";
  let num = get_line() in 
    try 
      if int_of_string num >= 0 
      then int_of_string num
      else 
        begin
          print_string "Invalid position\n";
          ask_num()
        end
    with
      | _ -> print_string "Invalid Position!\n"; ask_num()

(** Ask for an expression. The argument f corresponds to the function
    that will parse the expression in the pure lambda, lambda sigma,
    lambda s_e or in the suspension calculus. *)
let rec ask_exp f = 
  print_string "Give an expression (or quit): ";
  let expression = get_line() in  
    if (expression = "Quit" || 
	expression = "quit" || 
	expression = "Exit" || 
	expression = "exit")
    then 
      raise Quit
    else 
      try
        (f expression);
        expression
      with Stream.Error _ ->  print_string "Invalid Expression!\n"; ask_exp f
	
