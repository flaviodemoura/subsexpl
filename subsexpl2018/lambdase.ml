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

(** This module contains the main loop for the lambda s_e calculus.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes
open Sematchlse
open Seredlse

let rec print_exp_lse exp = 
  match exp with 
    | Dummy -> print_string "\\diamondsuit"
    | DB i -> print_int i
    | Vr c -> print_string c
    | A(e1,e2) ->
        print_string "(";
        print_exp_lse e1;
        print_string "  ";
        print_exp_lse e2;
        print_string ")"
    | L(e1,_,_) -> 
        print_string "\\lambda(";
        print_exp_lse e1;
        print_string ")"
    | S(i,e1,e2) -> 
        print_string "(";
         print_exp_lse e1;
        print_string "  \\sigma^";
        print_int i;
        print_string "  ";
         print_exp_lse e2;
        print_string ")"
    | P(j,k,e1) -> 
        print_string "\\phi^"; 
        print_int j;
        print_string "_";
        print_int k;
        print_string "("; 
        print_exp_lse e1;
        print_string ")"
    | _ -> assert false

(** This function takes an expression exp as argument and generates a list of pairs of the form (rule name, positions where this rule apply). *)
let lst_lse exp = 
  [
    ("Sigma-generation: ",(matchingBeta2 exp [] []));
    ("Sigma-Lambda-transition: ",(matchingSLtransition exp [] []));
    ("Sigma-App-transition: ",(matchingSAtransition exp [] []));
    ("Sigma-destruction: ",(matchingSDtransition exp [] []));
    ("Phi-Lambda-transition: ",(matchingPLtransition exp [] []));
    ("Phi-App-transition: ",(matchingPAtransition exp [] []));
    ("Phi-destruction: ",(matchingPDtransition exp [] []));
    ("Sigma-Sigma-transition: ",(matchingSStransition exp [] []));
    ("Sigma-Phi-transition 1: ",(matchingSPtransition1 exp [] []));
    ("Sigma-Phi-transition 2: ",(matchingSPtransition2 exp [] []));
    ("Phi-Sigma-transition: ",(matchingPStransition exp [] []));
    ("Phi-Phi-transition 1: ",(matchingPPtransition1 exp [] []));
    ("Phi-Phi-transition 2: ",(matchingPPtransition2 exp [] []));
    ("Eta: ",(matchingETA exp [] []));
    ("One beta full step (leftmost): ",(matchingBeta2 exp [] []));
    ("One beta full step (random): ",(matchingBeta2 exp [] []));
    ("Lambda s_e rules (dvi).", [])
  ]

(** This is an auxiliary function used by the normalisation function. *)
let lredices2 exp =
    if ( ((matchingSLtransition exp [] []) <> [])      or 
         ((matchingSAtransition exp [] []) <> [])      or
         ((matchingSDtransition exp [] []) <> [])      or
         ((matchingPLtransition exp [] []) <> [])      or
         ((matchingPAtransition exp [] []) <> [])      or
         ((matchingPDtransition exp [] []) <> [])      or
         ((matchingSStransition exp [] []) <> [])      or
         ((matchingSPtransition1 exp [] []) <> [])     or
         ((matchingSPtransition2 exp [] []) <> [])     or
         ((matchingPStransition exp [] []) <> [])      or
         ((matchingPPtransition1 exp [] []) <> [])     or
         ((matchingPPtransition2 exp [] []) <> []) ) then true else false
      
(** This is the normalisation function. *)
let ran_normal_lse expinit  pos =
  let l_upl = ref [(expinit,1,pos,"\\sigma\\mbox{-{\\scriptsize gen}}")] in
  let exp = ref expinit in 
  let posit = ref [0] in
    while (lredices2 !exp) do 
      while (matchingSLtransition !exp [] []) <> [] do
        posit := (List.hd (matchingSLtransition !exp [] []));
	exp := (sltransition !exp !posit);
	l_upl := ((!exp,2,!posit,"\\sigma\\lambda") :: !l_upl)
      done;ignore !exp;
      while (matchingSAtransition !exp [] []) <> [] do
	posit := (List.hd (matchingSAtransition !exp [] []));
        exp := (satransition !exp !posit);
	l_upl := ((!exp,3,!posit,"\\sigma\\mbox{-{\\scriptsize app}}") :: !l_upl)
      done;ignore !exp; 
      while (matchingSDtransition !exp [] []) <> [] do
        posit := (List.hd (matchingSDtransition !exp [] []));
	exp := (sdtransition !exp !posit);
	l_upl := ((!exp,4,!posit,"\\sigma\\mbox{-{\\scriptsize des}}") :: !l_upl)
      done;ignore !exp;
      while (matchingPLtransition !exp [] []) <> [] do
        posit := (List.hd (matchingPLtransition !exp [] []));
	exp := (pltransition !exp !posit);
	l_upl := ((!exp,5,!posit,"\\varphi\\lambda") :: !l_upl)
      done;ignore !exp;
      while (matchingPAtransition !exp [] []) <> [] do
        posit := (List.hd (matchingPAtransition !exp [] []));
	exp := (patransition !exp !posit);
	l_upl := ((!exp,6,!posit,"\\varphi\\mbox{-{\\scriptsize app}}") :: !l_upl)
      done;ignore !exp;
      while (matchingPDtransition !exp [] []) <> [] do
        posit := (List.hd (matchingPDtransition !exp [] []));
	exp := (pdtransition !exp !posit);
	l_upl := ((!exp,7,!posit,"\\varphi\\mbox{-{\\scriptsize des}}") :: !l_upl)
      done;ignore !exp;
      while (matchingSStransition !exp [] []) <> [] do
        posit := (List.hd (matchingSStransition !exp [] []));
	exp := (sstransition !exp !posit);
	l_upl := ((!exp,8,!posit,"\\sigma\\sigma") :: !l_upl)
      done;ignore !exp;
      while (matchingSPtransition1 !exp [] []) <> [] do
        posit := (List.hd (matchingSPtransition1 !exp [] []));
	exp := (sptransition1 !exp !posit);
	l_upl := ((!exp,9,!posit,"\\sigma\\varphi_1") :: !l_upl)
      done;ignore !exp;
      while (matchingSPtransition2 !exp [] []) <> [] do
        posit := (List.hd (matchingSPtransition2 !exp [] []));
	exp := (sptransition2 !exp !posit);
	l_upl := ((!exp,10,!posit,"\\sigma\\varphi_2") :: !l_upl)
      done;ignore !exp;
      while (matchingPStransition !exp [] []) <> [] do
        posit := (List.hd (matchingPStransition !exp [] []));
	exp := (pstransition !exp !posit);
	l_upl := ((!exp,11,!posit,"\\varphi\\sigma") :: !l_upl)
      done;ignore !exp;
      while (matchingPPtransition1 !exp [] []) <> [] do
        posit := (List.hd (matchingPPtransition1 !exp [] []));
	exp := (pptransition1 !exp !posit);
	l_upl := ((!exp,12,!posit,"\\varphi\\varphi_1") :: !l_upl)
      done;ignore !exp;
      while (matchingPPtransition2 !exp [] []) <> [] do
        posit := (List.hd (matchingPPtransition2 !exp [] []));
	exp := (pptransition2 !exp !posit);
	l_upl := ((!exp,13,!posit,"\\varphi\\varphi_2") :: !l_upl)
      done;ignore !exp;
    done;
    !l_upl

(** This function search for the leftmost redex of the given expression [exp] in the lambda s_e calculus. It returns a pair of the form (the leftmost redex of the given expression [exp],the rule number corresponding to this redex). *)
let rec left_red_lse exp pos = 
  match exp with 
    | A(e1,e2) -> 
        let aux = (left_red_lse e1 (List.append pos [1])) in 
          if aux = ([],0) 
          then (left_red_lse e2 (List.append pos [2]))
          else aux
    | L(e,_,_) -> (left_red_lse e (List.append pos [1]))
    | S(j,e1,e2) -> 
        let aux1 = 
          (match e1 with
             | L(e,_,_) -> (pos,2)
             | A(ex1,ex2) -> (pos,3)
             | DB n -> (pos,4)
             | S(i,ex1,ex2) -> (if i <= j
                                then (pos,8)
                                else 
                                  let aux = (left_red_lse ex1 (List.append pos [1;1])) in
                                    if  aux = ([],0)
                                    then (left_red_lse ex2 (List.append pos [1;2]))
                                    else aux)  
             | P(i,k,e) -> (if k<j && j<k+i
                            then (pos,9)
                            else (if k+i<=j 
                                  then (pos,10)
                                  else left_red_lse e (List.append pos [1;1]))) 
             | _ -> ([],0)) in
          if aux1 = ([],0) 
          then (left_red_lse e2 (List.append pos [2]))
          else aux1
    | P(i,k,e) -> 
        (match e with
           | L(ex,_,_) -> (pos,5)
           | A(ex1,ex2) -> (pos,6)
           | DB n -> (pos,7)
           | S(j,e1,e2) -> 
               let aux = (if j <= k+1
                          then (pos,11)
                          else (left_red_lse e1 (List.append pos [1;1]))) in
                 if aux = ([],0) 
                 then (left_red_lse e2 (List.append pos [1;2]))
                 else (left_red_lse e2 (List.append pos [2]))
           | P(j,m,ex) -> (if m+j <= k 
                           then (pos,12)
                           else (if (m <= k && k < m+j) 
                                 then (pos,13)
                                 else left_red_lse ex (List.append pos [1;1])))
           | _ -> ([],0))
    | _ -> ([],0)

(** [reduce_lse] takes as argument a lambda s_e expression [ex], an interger [rule_number], an integer list [position] and a list of 4-uples and return a new list of 4-uples which contains a new 4-uple formed by the expression [ex] reduced by the rule corresponding to [rule_number] at position [position], and [left_norm_lse] is the normalisation function for the lambda s_e calculus implemented with the leftmost/outermost strategy. *)
let rec reduce_lse ex rule_number position l_upl = 
  match rule_number with 
    | 1 -> (((betareduction2 ex position),rule_number,position,"\\sigma\\mbox{-{\\scriptsize gen}}") :: l_upl)
    | 2 -> (((sltransition ex position),rule_number,position,"\\sigma\\lambda") :: l_upl)
    | 3 -> (((satransition ex position),rule_number,position,"\\sigma\\mbox{-{\\scriptsize app}}") :: l_upl)
    | 4 -> (((sdtransition ex position),rule_number,position,"\\sigma\\mbox{-{\\scriptsize des}}") :: l_upl)
    | 5 -> (((pltransition ex position),rule_number,position,"\\varphi\\lambda") :: l_upl)
    | 6 -> (((patransition ex position),rule_number,position,"\\varphi\\mbox{-{\\scriptsize app}}") :: l_upl)
    | 7 -> (((pdtransition ex position),rule_number,position,"\\varphi\\mbox{-{\\scriptsize des}}") :: l_upl)
    | 8 -> (((sstransition ex position),rule_number,position,"\\sigma\\sigma") :: l_upl)
    | 9 -> (((sptransition1 ex position),rule_number,position,"\\sigma\\varphi 1") :: l_upl)
    | 10 -> (((sptransition2 ex position),rule_number,position,"\\sigma\\varphi 2") :: l_upl)
    | 11 -> (((pstransition ex position),rule_number,position,"\\varphi\\sigma") :: l_upl)
    | 12 -> (((pptransition1 ex position),rule_number,position,"\\varphi\\varphi 1") :: l_upl)
    | 13 -> (((pptransition2 ex position),rule_number,position,"\\varphi\\varphi 2") :: l_upl)
    | 14 -> (((etatransition ex position),rule_number,position,"Eta") :: l_upl)
    | 15 -> (List.append (left_norm_lse ex position) l_upl)
    | 16 -> (List.append (ran_normal_lse (betareduction2 ex position) position) l_upl)
    | _ -> assert false       
and
  left_norm_lse expinit pos = 
  let l_upl = ref [(expinit,1,pos,"\\sigma\\mbox{-{\\scriptsize gen}}")] in 
  let exp = ref (betareduction2 expinit pos) in 
  let posit = ref ([]:int list) in
    while (left_red_lse !exp []) <> ([],0) do
      posit := Pervasives.fst(left_red_lse !exp []);
      l_upl :=  reduce_lse !exp (Pervasives.snd(left_red_lse !exp [])) !posit !l_upl;
        exp := (Common.first(List.hd !l_upl))
    done;
    !l_upl
              
(** This is the main loop for the lambda s_e calculus. *)
let rec lse f =
  try
    let init_exp = Input.ask_exp Selexerlse.convertStr2Exp_lse in
    let i_upl = [((Selexerlse.convertStr2Exp_lse init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = lst_lse c_exp in
        print_newline();
        print_string "Expression: ";
        print_exp_lse c_exp;
        print_newline();
        Output.display_opt_menu lst_ex;
        let r_num = Input.ask_num() in
          if (r_num < 17) 
          then 
            begin
              let l_pos = 
                if r_num > 14 
                then Pervasives.snd(List.nth lst_ex 0)
                else Pervasives.snd(List.nth lst_ex (r_num-1))
              in
                if (List.length l_pos) <> 0 
                then
                  begin 
	            let position = Input.ask_pos l_pos in 
                    let c_upl = reduce_lse c_exp r_num position l_upl in
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
	        | 17 -> 
                    ignore (Output.print_in_latex "serules" 2);
                    internal_loop l_upl
	        | 18 -> 
                    internal_loop (List.tl l_upl)
	        | 19 ->
		    print_newline();
		    Output.print_history (List.rev l_upl) print_exp_lse; 
		    ignore (Input.get_line ());       
		    internal_loop l_upl
	        | 20 -> 
		    ignore (Output.latex_output l_upl);
		    internal_loop l_upl
	        | 21 -> 
                    Output.save_red l_upl init_exp 2;
                    internal_loop l_upl
	        | 22 -> 
		    Output.ask_save l_upl init_exp 2;
		    internal_loop i_upl
	        | 23 -> 
		    Output.ask_save l_upl init_exp 2;
		    f()
	        | 24 -> 
		    Output.ask_save l_upl init_exp 2;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  
