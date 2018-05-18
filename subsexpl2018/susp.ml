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

(** This module contains the main loop for the suspension calculus.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes
open Sematchsus
open Seredsus

let rec print_exp_sus exp = 
  match exp with 
    | Dummy -> print_string "\\diamondsuite"
    | DB i -> print_int i
    | Vr c -> print_string c
    | A(e1,e2) -> 
        print_string "(";
        print_exp_sus e1;
        print_string "  ";
        print_exp_sus e2;
        print_string ")"
    | L(e1,_,_) -> 
        print_string "\\lambda(";
        print_exp_sus e1;
        print_string ")"
    | Sp(e1,i,j,env) -> 
        print_string "[[";
        print_exp_sus e1;
        print_string ",";
        print_int i;
        print_string ",";
        print_int j;
        print_string ",";
        print_env env;
        print_string "]]"
    | _ -> assert false
and print_env env =
  match env with
    | Nilen -> print_string "nil"
    | Con(envt,env1) ->
        print_envt envt;
        print_string "::";
        print_env env1
    | Ck(env1,i,j,env2) -> 
        print_string "{{";
        print_env env1;
        print_string ",";
        print_int i;
        print_string ",";
        print_int j;
        print_string ",";
        print_env env2;
        print_string "}}"
and print_envt envt =
  match envt with   
    | Ar i -> 
        print_string "@";
        print_int i
    | Paar(exp1,i) -> 
        print_string "(";
        print_exp_sus exp1;       
        print_string ",";
        print_int i;
        print_string ")"
    | LG(envt1,i,j,env1) -> 
        print_string "\\langle \\langle";
        print_envt envt1;
        print_string  ",";
        print_int i; 
        print_string  ",";
        print_int j;
        print_string  ","; 
        print_env env1;
        print_string "\\rangle \\rangle " 

(** This function takes an expression exp as argument and generates a list of pairs of the form (rule name, positions where this rule apply). *)
let lst_sus exp = 
  [
    ("Betas: ",(matchingBetas exp [] []));
    ("r1: ",(matching_r1 exp [] []));
    ("r2: ",(matching_r2 exp [] []));
    ("r3: ",(matching_r3 exp [] []));
    ("r4: ",(matching_r4 exp [] []));
    ("r5: ",(matching_r5 exp [] []));
    ("r6: ",(matching_r6 exp [] []));
    ("r7: ",(matching_r7 exp [] []));
    ("Eta: ",(matching_Eta exp [] []));
    ("m1: ",(matching_m1 exp [] []));
    ("m2: ",(matching_m2 exp [] []));
    ("m3: ",(matching_m3 exp [] []));
    ("m4: ",(matching_m4 exp [] []));
    ("m5: ",(matching_m5 exp [] []));
    ("m6: ",(matching_m6 exp [] []));
    ("m7: ",(matching_m7 exp [] []));
    ("m8: ",(matching_m8 exp [] []));
    ("m9: ",(matching_m9 exp [] []));
    ("m10: ",(matching_m10 exp [] []));
    ("One beta full step (leftmost): ",(matchingBetas exp [] []));
    ("One beta full step (random): ",(matchingBetas exp [] []));
    ("Suspension rules (dvi).", [])
  ]

(** This is an auxiliary function for the 'random' normalisation function. *)
let lredices3 exp =
  if ( ((matching_r1 exp [] []) <> [])      or
       ((matching_r2 exp [] []) <> [])      or
       ((matching_r3 exp [] []) <> [])      or
       ((matching_r4 exp [] []) <> [])      or
       ((matching_r5 exp [] []) <> [])      or
       ((matching_r6 exp [] []) <> [])      or
       ((matching_r7 exp [] []) <> [])      or
       ((matching_m1 exp [] []) <> [])      or
       ((matching_m2 exp [] []) <> [])      or
       ((matching_m3 exp [] []) <> [])      or
       ((matching_m4 exp [] []) <> [])      or
       ((matching_m5 exp [] []) <> [])      or
       ((matching_m6 exp [] []) <> [])      or
       ((matching_m7 exp [] []) <> [])      or
       ((matching_m8 exp [] []) <> [])      or
       ((matching_m9 exp [] []) <> [])      or
       ((matching_m10 exp [] []) <> []) ) then true else false

(** This is the 'randon' normalisation function for the suspension calculus. *)
let ran_normal_sus expinit pos =
  let l_trp = ref [(expinit,1,pos,"\\beta_s")] in
  let exp = ref expinit in 
  let posit = ref [0] in
    while (lredices3 !exp) do 
      while (matching_r1 !exp [] []) <> [] do
        posit := (List.hd (matching_r1 !exp [] []));
	exp := (r1_reduction !exp !posit);
	l_trp := ((!exp,2,!posit,"r_1") :: !l_trp)
      done;ignore !exp;
      while (matching_r2 !exp [] []) <> [] do
        posit := (List.hd (matching_r2 !exp [] []));
	exp := (r2_reduction !exp !posit);
	l_trp := ((!exp,3,!posit,"r_2") :: !l_trp)
      done;ignore !exp;
      while (matching_r3 !exp [] []) <> [] do
        posit := (List.hd (matching_r3 !exp [] []));
	exp := (r3_reduction !exp !posit);
	l_trp := ((!exp,4,!posit,"r_3") :: !l_trp)
      done;ignore !exp;
      while (matching_r4 !exp [] []) <> [] do
 	posit := (List.hd (matching_r4 !exp [] []));
        exp := (r4_reduction !exp !posit);
	l_trp := ((!exp,5,!posit,"r_4") :: !l_trp)
      done;ignore !exp;
      while (matching_r5 !exp [] []) <> [] do
        posit := (List.hd (matching_r5 !exp [] []));
	exp := (r5_reduction !exp !posit);
	l_trp := ((!exp,6,!posit,"r_5") :: !l_trp)
      done;ignore !exp;
      while (matching_r6 !exp [] []) <> [] do
        posit := (List.hd (matching_r6 !exp [] []));
	exp := (r6_reduction !exp !posit);
	l_trp := ((!exp,7,!posit,"r_6") :: !l_trp)
      done;ignore !exp;
      while (matching_r7 !exp [] []) <> [] do
        posit := (List.hd (matching_r7 !exp [] []));
	exp := (r7_reduction !exp !posit);
	l_trp := ((!exp,8,!posit,"r_7") :: !l_trp)
      done;ignore !exp;
      while (matching_m1 !exp [] []) <> [] do
        posit := (List.hd (matching_m1 !exp [] []));
	exp := (m1_reduction !exp !posit);
	l_trp := ((!exp,9,!posit,"m_1") :: !l_trp)
      done;ignore !exp;
      while (matching_m2 !exp [] []) <> [] do
        posit := (List.hd (matching_m2 !exp [] []));
	exp := (m2_reduction !exp !posit);
	l_trp := ((!exp,10,!posit,"m_2") :: !l_trp)
		done;ignore !exp;
      while (matching_m3 !exp [] []) <> [] do
        posit := (List.hd (matching_m3 !exp [] []));
	exp := (m3_reduction !exp !posit);
	l_trp := ((!exp,11,!posit,"m_3") :: !l_trp)
      done;ignore !exp;
      while (matching_m4 !exp [] []) <> [] do
        posit := (List.hd (matching_m4 !exp [] []));
	exp := (m4_reduction !exp !posit);
	l_trp := ((!exp,12,!posit,"m_4") :: !l_trp)
      done;ignore !exp;
      while (matching_m5 !exp [] []) <> [] do
        posit := (List.hd (matching_m5 !exp [] []));
	exp := (m5_reduction !exp !posit);
	l_trp := ((!exp,13,!posit,"m_5") :: !l_trp)
      done;ignore !exp;
      while (matching_m6 !exp [] []) <> [] do
        posit := (List.hd (matching_m6 !exp [] []));
 	exp := (m6_reduction !exp !posit);
	l_trp := ((!exp,14,!posit,"m_6") :: !l_trp)
      done;ignore !exp;
      while (matching_m7 !exp [] []) <> [] do
        posit := (List.hd (matching_m7 !exp [] []));
	exp := (m7_reduction !exp !posit);
	l_trp := ((!exp,15,!posit,"m_7") :: !l_trp)
      done;ignore !exp;
      while (matching_m8 !exp [] []) <> [] do
        posit := (List.hd (matching_m8 !exp [] []));
	exp := (m8_reduction !exp !posit);
	l_trp := ((!exp,16,!posit,"m_8") :: !l_trp)
      done;ignore !exp;
      while (matching_m9 !exp [] []) <> [] do
        posit := (List.hd (matching_m9 !exp [] []));
	exp := (m9_reduction !exp !posit);
	l_trp := ((!exp,17,!posit,"m_9") :: !l_trp)
      done;ignore !exp;
      while (matching_m10 !exp [] []) <> [] do
        posit := (List.hd (matching_m10 !exp [] []));
	exp := (m10_reduction !exp !posit);
	l_trp := ((!exp,18,!posit,"m_{10}") :: !l_trp)
      done;ignore !exp;
    done;
    !l_trp

(** This function search for the leftmost redex of the given expression [exp] in the lambda sigma calculus. It returns a pair of the form (the leftmost redex of the given expression [exp],the rule number corresponding to this redex). *)
let rec left_red_sus exp pos = 
  match exp with 
    | A(e1,e2) -> 
        let aux = (left_red_sus e1 (List.append pos [1])) in 
          if aux = ([],0) 
          then (left_red_sus e2 (List.append pos [2]))
          else aux
    | L(ex,_,_) -> (left_red_sus ex (List.append pos [1]))
    | Sp(Vr c,i,j,env) -> (pos,2)
    | Sp(DB i,0,j,Nilen) -> (pos,3)
    | Sp(DB 1,i,j,env) -> 
        (match env with
           | Con(Ar(k),env) -> (pos,4)
           | Con(Paar(e1,k),env) -> (pos,5)
           | _ -> left_red_sus_env env (List.append pos [2]))
    | Sp(DB i,j,k,env) -> 
        if i > 1 
        then
          match env with 
            | Con(envt,env) -> (pos,6)
            | _ -> left_red_sus_env env (List.append pos [2])
        else ([],0)
    | Sp(ex,i,j,env) -> 
        (match ex with 
           | A(e1,e2) -> (pos,7)
           | L(ex,_,_) -> (pos,8)
           | Sp(e1,i1,j1,env1) -> (pos,10)
           | _ -> 
               let aux = left_red_sus ex (List.append pos [1]) in 
                 if aux = ([],0)
                 then left_red_sus_env env (List.append pos [2])
                 else aux)
    | _ -> ([],0)
and 
left_red_sus_env env pos = 
  match env with
    | Ck(Nilen,_,0,Nilen) -> (pos,11)
    | Ck(Nilen,0,_,env) -> (pos,13)
    | Ck(Nilen,i,j,Con(et,en)) -> 
        if (i>0) && (j>0)
        then (pos,12)
        else ([],0)
    | Ck(env1,_,_,env2) ->
        (match env1 with 
           | Con(et,en) -> (pos,14)
           | _ -> 
               let aux = left_red_sus_env env1 (List.append pos [1]) in
                 if aux = ([],0)
                 then left_red_sus_env env2 (List.append pos [2])
                 else aux)
    | Con(et,en) ->
        let aux = left_red_sus_envt et (List.append pos [1]) in
          if aux = ([],0)
          then left_red_sus_env en (List.append pos [2])
          else aux
    | Nilen -> ([],0)
and
  left_red_sus_envt envt pos = 
  match envt with 
    | LG(et,_,0,Nilen) -> (pos,15)
    | LG(Ar(k),i,_,en) ->
        if i = k+1
        then
          (match en with
             | Con(Ar(m),e2) -> (pos,16)
             | Con(Paar(ex,m),e2) -> (pos,17)
             | _ -> left_red_sus_env en (List.append pos [2]))
        else left_red_sus_env en (List.append pos [2])
    | LG(Paar(ex,m),_,_,Con(et,en)) -> (pos,18)
    | LG(et1,i,_,Con(et2,en)) ->
        if i <> Sematchsus.ind et1
        then (pos,19)
        else let aux = left_red_sus_envt et1 (List.append pos [1]) in 
          if aux = ([],0) 
          then let aux1 = left_red_sus_envt et2 (List.append pos [2;1]) in 
            if aux1 = ([],0)
            then left_red_sus_env en (List.append pos [2;2])
            else aux1
          else aux
    | Paar(ex,m) -> left_red_sus ex (List.append pos [1])
    | _ -> ([],0)
            
(** [reduce_sus] takes as argument a suspended expression [ex], an interger [rule_number], an integer list [position] and a list of 4-uples and return a new list of 4-uples which contains a new 4-uple formed by the expression [ex] reduced by the rule corresponding to [rule_number] at position [position]. *)
let rec reduce_sus ex rule_number position l_upl =
	  match rule_number with 
	    | 1 -> (((betasreduction ex position),rule_number,position,"\\beta_s") :: l_upl)
	    | 2 -> (((r1_reduction ex position),rule_number,position,"r_1") :: l_upl)
	    | 3 -> (((r2_reduction ex position),rule_number,position,"r_2") :: l_upl)
	    | 4 -> (((r3_reduction ex position),rule_number,position,"r_3") :: l_upl)
	    | 5 -> (((r4_reduction ex position),rule_number,position,"r_4") :: l_upl)
	    | 6 -> (((r5_reduction ex position),rule_number,position,"r_5") :: l_upl)
	    | 7 -> (((r6_reduction ex position),rule_number,position,"r_6") :: l_upl)
	    | 8 -> (((r7_reduction ex position),rule_number,position,"r_7") :: l_upl)
	    | 9 -> (((eta_reduction ex position),rule_number,position,"Eta") :: l_upl)
            | 10 -> (((m1_reduction ex position),rule_number,position,"m_1") :: l_upl)
            | 11 -> (((m2_reduction ex position),rule_number,position,"m_2") :: l_upl)
            | 12 -> (((m3_reduction ex position),rule_number,position,"m_3") :: l_upl)
            | 13 -> (((m4_reduction ex position),rule_number,position,"m_4") :: l_upl)
            | 14 -> (((m5_reduction ex position),rule_number,position,"m_5") :: l_upl)
            | 15 -> (((m6_reduction ex position),rule_number,position,"m_6") :: l_upl)
            | 16 -> (((m7_reduction ex position),rule_number,position,"m_7") :: l_upl)
            | 17 -> (((m8_reduction ex position),rule_number,position,"m_8") :: l_upl)
            | 18 -> (((m9_reduction ex position),rule_number,position,"m_9") :: l_upl)
            | 19 -> (((m10_reduction ex position),rule_number,position,"m_{10}") :: l_upl)
            | 20 -> (List.append (left_norm_sus ex position) l_upl)
            | 21 -> (List.append (ran_normal_sus (betasreduction ex position) position) l_upl)  
	    | _ -> assert false 
and
  left_norm_sus expinit pos = 
  let l_upl = ref [(expinit,1,pos,"\\beta_s")] in 
  let exp = ref (betasreduction expinit pos) in 
  let posit = ref ([]:int list) in
    while (left_red_sus !exp []) <> ([],0) do
      posit := Pervasives.fst(left_red_sus !exp []);
      l_upl := reduce_sus !exp (Pervasives.snd(left_red_sus !exp [])) !posit !l_upl;
      exp := (Common.first(List.hd !l_upl))
    done;
    !l_upl
                
(** This is the main loop for the suspension calculus. *)
let rec lsusp f =
  try
    let init_exp = Input.ask_exp Selexersus.convertStr2Exp_sus in
    let i_upl = [((Selexersus.convertStr2Exp_sus init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = lst_sus c_exp in
        print_newline();
        print_string "Expression: ";
        print_exp_sus c_exp;
        print_newline();
        Output.display_opt_menu lst_ex;
        let r_num = Input.ask_num() in
          if (r_num < 22) 
          then 
            begin
              let l_pos = 
                if r_num > 19 
                then Pervasives.snd(List.nth lst_ex 0)
                else Pervasives.snd(List.nth lst_ex (r_num-1))
              in
                if (List.length l_pos) <> 0 
                then
                  begin 
	            let position = Input.ask_pos l_pos in 
                    let c_upl = reduce_sus c_exp r_num position l_upl in
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
	        | 22 -> 
                    ignore (Output.print_in_latex "susprules" 3);
                    internal_loop l_upl
	        | 23 -> 
                    internal_loop (List.tl l_upl)
	        | 24 ->
		    print_newline();
		    Output.print_history (List.rev l_upl) print_exp_sus; 
		    ignore (Input.get_line ());       
		    internal_loop l_upl
	        | 25 -> 
		    ignore (Output.latex_output l_upl);
		    internal_loop l_upl
	        | 26 -> 
                    Output.save_red l_upl init_exp 3;
                    internal_loop l_upl
	        | 27 -> 
		    Output.ask_save l_upl init_exp 3;
		    internal_loop i_upl
	        | 28 -> 
		    Output.ask_save l_upl init_exp 3;
		    f()
	        | 29 -> 
		    Output.ask_save l_upl init_exp 3;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  
