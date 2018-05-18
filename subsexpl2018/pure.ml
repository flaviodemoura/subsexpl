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

(** This module contains the main loop for the pure lambda calculus. This simulation uses the lambda s_e calculus of explicit substitutions.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes
   
(** This is the main loop used for the simulation of the pure lambda calculus. *)
let rec lpure f =
  try
    let init_exp = Input.ask_exp Selexerlse.convertStr2Exp_lse in
    let i_upl = [((Selexerlse.convertStr2Exp_lse init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = Sepure.lst_pure c_exp in
        print_newline();
        print_string "Expression: ";
        Lambdase.print_exp_lse c_exp;
        print_newline();
        Output.display_opt_menu lst_ex;
        let r_num = Input.ask_num() in
          if (r_num < 3) 
          then 
            begin
              let l_pos = Pervasives.snd(List.nth lst_ex (r_num-1))
              in
                if (List.length l_pos) <> 0 
                then
                  begin 
	            let position = Input.ask_pos l_pos in 
                    let c_upl = Sepure.reduce_pure c_exp r_num position l_upl in 
                      internal_loop c_upl 
                  end
                else 
                  begin
                    print_string "No redexes for this rule. Try again.\n";
                    internal_loop l_upl
                  end
            end
          else
            begin
	      match r_num with
	        | 3 -> 
                    let c_upl = Sepure.beta_normout l_upl in
                      internal_loop c_upl
                | 4 ->
                    let c_upl = Sepure.beta_normin l_upl in
                      internal_loop c_upl
                | 5 -> internal_loop (List.tl l_upl)
	        | 6 ->
		    print_newline ();
		    Output.print_history (List.rev l_upl) Lambdase.print_exp_lse; 
		    Input.get_line ();       
		    internal_loop l_upl
	        | 7 -> 
		    Output.latex_output l_upl;
		    internal_loop l_upl
	        | 8 -> 
                    Output.save_red l_upl init_exp 0;
                    internal_loop l_upl
	        | 9 -> 
		    Output.ask_save l_upl init_exp 0;
		    internal_loop i_upl
	        | 10 -> 
		    Output.ask_save l_upl init_exp 0;
		    f()
	        | 11 -> 
		    Output.ask_save l_upl init_exp 0;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  


(** This is the main loop used for the simulation of the pure lambda calculus with suspcomb. *)
let rec lpurecomb f =
  try
    let init_exp = Input.ask_exp Selexersuscomb.convertStr2Exp_suscomb in
    let i_upl = [((Selexersuscomb.convertStr2Exp_suscomb init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = Sepure.lst_purecomb c_exp in
        print_newline();
        print_string "Expression: ";
        Suspcomb.print_exp_suscomb c_exp;
        print_newline();
        Output.display_opt_menu lst_ex;
        let r_num = Input.ask_num() in
          if (r_num < 3) 
          then 
            begin
              let l_pos = Pervasives.snd(List.nth lst_ex (r_num-1))
              in
                if (List.length l_pos) <> 0 
                then
                  begin 
	            let position = Input.ask_pos l_pos in 
                    let c_upl = Sepure.reduce_purecomb c_exp r_num position l_upl in 
                      internal_loop c_upl 
                  end
                else 
                  begin
                    print_string "No redexes for this rule. Try again.\n";
                    internal_loop l_upl
                  end
            end
          else
            begin
	      match r_num with
	        | 3 -> 
                    let c_upl = Sepure.beta_normoutcomb l_upl in
                      internal_loop c_upl
                | 4 ->
                    let c_upl = Sepure.beta_normincomb l_upl in
                      internal_loop c_upl
                | 5 -> internal_loop (List.tl l_upl)
	        | 6 ->
		    print_newline ();
		    Output.print_history (List.rev l_upl) Suspcomb.print_exp_suscomb; 
		    Input.get_line ();       
		    internal_loop l_upl
	        | 7 -> 
		    Output.latex_output l_upl;
		    internal_loop l_upl
	        | 8 -> 
                    Output.save_red l_upl init_exp 0;
                    internal_loop l_upl
	        | 9 -> 
		    Output.ask_save l_upl init_exp 0;
		    internal_loop i_upl
	        | 10 -> 
		    Output.ask_save l_upl init_exp 0;
		    f()
	        | 11 -> 
		    Output.ask_save l_upl init_exp 0;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  
