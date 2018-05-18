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

(** This module contains the main loop for the combining suspension calculus.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes
open Sematchsuscomb
open Seredsuscomb

let rec print_exp_suscomb exp = 
  match exp with 
    | Dummy -> print_string "\\diamondsuite"
    | DB i -> print_int i
    | Vr c -> print_string c
    | A(e1,e2) -> 
        print_string "(";
        print_exp_suscomb e1;
        print_string "  ";
        print_exp_suscomb e2;
        print_string ")"
    | L(e1,_,_) -> 
        print_string "\\lambda(";
        print_exp_suscomb e1;
        print_string ")"
    | Sp(e1,i,j,env) -> 
        print_string "[[";
        print_exp_suscomb e1;
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
and print_envt envt =
  match envt with   
    | Ar i -> 
        print_string "@";
        print_int i;
    | Paar(exp1,i) -> 
        print_string "(";
        print_exp_suscomb exp1;       
        print_string ",";
        print_int i;
        print_string ")"
 
(** This function takes an expression exp as argument and generates a list of pairs of the form (rule name, positions where this rule apply). *)
let lst_suscomb exp = 
  [
    ("Betas: ",(matchingBetascomb exp [] []));
    ("BetasP: ",(matchingBetascombL exp [] []));
    ("r1: ",(matching_combr1 exp [] []));
    ("r2: ",(matching_combr2 exp [] []));
    ("r3: ",(matching_combr3 exp [] []));
    ("r4: ",(matching_combr4 exp [] []));
    ("r5: ",(matching_combr5 exp [] []));
    ("r6: ",(matching_combr6 exp [] []));
    ("r7: ",(matching_combr7 exp [] []));
    ("r8: ",(matching_combr8 exp [] []));
    ("r9: ",(matching_combr9 exp [] []));
    ("r10: ",(matching_combr10 exp [] []));
    ("r11: ",(matching_combr11 exp [] []));
    ("Eta: ",(matching_Etascomb exp [] []));
    ("One beta full step (leftmost): ",(matchingBetascomb exp [] []));
    ("One beta full step (random): ",(matchingBetascomb exp [] []));
    ("Combining suspension rules (dvi).", [])
  ]

(** This is an auxiliary function for the 'random' normalisation function. *)
let lredices4 exp =
  if ( ((matching_combr1 exp [] []) <> [])      or
       ((matching_combr2 exp [] []) <> [])      or
       ((matching_combr3 exp [] []) <> [])      or
       ((matching_combr4 exp [] []) <> [])      or
       ((matching_combr5 exp [] []) <> [])      or
       ((matching_combr6 exp [] []) <> [])      or
       ((matching_combr7 exp [] []) <> [])      or
       ((matching_combr8 exp [] []) <> [])      or
       ((matching_combr9 exp [] []) <> [])      or
       ((matching_combr10 exp [] []) <> [])      or
       ((matching_combr11 exp [] []) <> []))  then true else false

(** This is the 'random' normalisation function for the suspension calculus. *)
let ran_normal_suscomb expinit pos =
  let l_trp = ref [(expinit,1,pos,"\\beta_s")] in
  let exp = ref expinit in 
  let posit = ref [0] in
    while (lredices4 !exp) do 
      while (matching_combr1 !exp [] []) <> [] do
        posit := (List.hd (matching_combr1 !exp [] []));
	exp := (r1_combreduction !exp !posit);
	l_trp := ((!exp,2,!posit,"r_1") :: !l_trp)
      done;!exp;
      while (matching_combr2 !exp [] []) <> [] do
        posit := (List.hd (matching_combr2 !exp [] []));
	exp := (r2_combreduction !exp !posit);
	l_trp := ((!exp,3,!posit,"r_2") :: !l_trp)
      done;!exp;
      while (matching_combr3 !exp [] []) <> [] do
        posit := (List.hd (matching_combr3 !exp [] []));
	exp := (r3_combreduction !exp !posit);
	l_trp := ((!exp,4,!posit,"r_3") :: !l_trp)
      done;!exp;
      while (matching_combr4 !exp [] []) <> [] do
 	posit := (List.hd (matching_combr4 !exp [] []));
        exp := (r4_combreduction !exp !posit);
	l_trp := ((!exp,5,!posit,"r_4") :: !l_trp)
      done;!exp;
      while (matching_combr5 !exp [] []) <> [] do
        posit := (List.hd (matching_combr5 !exp [] []));
	exp := (r5_combreduction !exp !posit);
	l_trp := ((!exp,6,!posit,"r_5") :: !l_trp)
      done;!exp;
      while (matching_combr6 !exp [] []) <> [] do
        posit := (List.hd (matching_combr6 !exp [] []));
	exp := (r6_combreduction !exp !posit);
	l_trp := ((!exp,7,!posit,"r_6") :: !l_trp)
      done;!exp;
      while (matching_combr7 !exp [] []) <> [] do
        posit := (List.hd (matching_combr7 !exp [] []));
	exp := (r7_combreduction !exp !posit);
	l_trp := ((!exp,8,!posit,"r_7") :: !l_trp)
      done;!exp;
      while (matching_combr8 !exp [] []) <> [] do
        posit := (List.hd (matching_combr8 !exp [] []));
	exp := (r8_combreduction !exp !posit);
	l_trp := ((!exp,9,!posit,"r_8") :: !l_trp)
      done;!exp;
      while (matching_combr9 !exp [] []) <> [] do
        posit := (List.hd (matching_combr9 !exp [] []));
	exp := (r9_combreduction !exp !posit);
	l_trp := ((!exp,10,!posit,"r_9") :: !l_trp)
      done;!exp;
      while (matching_combr10 !exp [] []) <> [] do
        posit := (List.hd (matching_combr10 !exp [] []));
	exp := (r10_combreduction !exp !posit);
	l_trp := ((!exp,11,!posit,"r_{10}") :: !l_trp)
      done;!exp;
      while (matching_combr11 !exp [] []) <> [] do
        posit := (List.hd (matching_combr11 !exp [] []));
	exp := (r11_combreduction !exp !posit);
	l_trp := ((!exp,12,!posit,"r_{11}") :: !l_trp)
      done;!exp;
    done;
    !l_trp

(** This function search for the leftmost redex of the given expression [exp] in the lambda sigma calculus. It returns a pair of the form (the leftmost redex of the given expression [exp],the rule number corresponding to this redex). *)
let rec left_red_suscomb exp pos = 
  match exp with 
    | A(e1,e2) -> 
        let aux = (left_red_suscomb e1 (List.append pos [1])) in 
          if aux = ([],0) 
          then (left_red_suscomb e2 (List.append pos [2]))
          else aux
    | L(e1,_,_) -> (left_red_suscomb e1 (List.append pos [1]))
    | Sp(Vr c,i,j,env) -> (pos,3) (** rule r_2 also applies, since constant/variables undiscriminated **)
    | Sp(DB i,j,k,env) ->  (if (i>j) then  (pos,5) 
                            else 
                            (if (isPaar (select env i)) then
                               (if (k=(indofPaar (select env i))) then (pos,12) 
                                 else 
                                 (if (isSusp (termofPaar (select env i))) then (pos,13)
                                  else (pos,7)))
                             else   
                             (if  (isAr (select env i)) then (pos,6)
                              else  left_red_suscomb_env env (List.append pos [2]))))
    | Sp(ex,i,j,env) -> 
       (if ((i=0) && (j=0) && (env=Nilen)) then (pos,11)
        else
        (if ((i=0) && (j<>0) && (env=Nilen)) then 
                       (match ex with 
                         | Sp(e1,i1,j1,env1) -> (pos,10)
                         | L(e1,_,_)    -> (pos,9)
                         | A(e1,e2) -> (pos,8)
                         | _ -> 
                             let aux = left_red_suscomb ex (List.append pos [1]) in 
                               if aux = ([],0)
                               then left_red_suscomb_env env (List.append pos [2])
                               else aux)
        else
        (match ex with
           | A(e1,e2) -> (pos,8)
           | L(e1,_,_)    -> (pos,9)
           | _ -> 
               let aux = left_red_suscomb ex (List.append pos [1]) in 
                 (if aux = ([],0)
                 then left_red_suscomb_env env (List.append pos [2])
                 else aux))))
    | _ -> ([],0)
and 
left_red_suscomb_env env pos = 
  match env with
    | Con(et,en) ->
        let aux = left_red_suscomb_envt et (List.append pos [1]) in
          if aux = ([],0)
          then left_red_suscomb_env en (List.append pos [2])
          else aux
    | _ -> ([],0)
and
  left_red_suscomb_envt envt pos = 
  match envt with 
    | Paar(ex,m) -> left_red_suscomb ex (List.append pos [1])
    | _ -> ([],0)
            
(** [reduce_suscomb] takes as argument a suspended expression [ex], an interger [rule_number], an integer list [position] and a list of 4-uples and return a new list of 4-uples which contains a new 4-uple formed by the expression [ex] reduced by the rule corresponding to [rule_number] at position [position]. *)
let rec reduce_suscomb ex rule_number position l_upl =
	  match rule_number with 
	    | 1 -> (((betasreductioncomb ex position),rule_number,position,"\\beta_s") :: l_upl)
	    | 2 -> (((betaLsreductioncomb ex position),rule_number,position,"\\beta_s\'") :: l_upl)
	    | 3 -> (((r1_combreduction ex position),rule_number,position,"r_1") :: l_upl)
	    | 4 -> (((r2_combreduction ex position),rule_number,position,"r_2") :: l_upl)
	    | 5 -> (((r3_combreduction ex position),rule_number,position,"r_3") :: l_upl)
	    | 6 -> (((r4_combreduction ex position),rule_number,position,"r_4") :: l_upl)
	    | 7 -> (((r5_combreduction ex position),rule_number,position,"r_5") :: l_upl)
	    | 8 -> (((r6_combreduction ex position),rule_number,position,"r_6") :: l_upl)
	    | 9 -> (((r7_combreduction ex position),rule_number,position,"r_7") :: l_upl)
            | 10 -> (((r8_combreduction ex position),rule_number,position,"r_8") :: l_upl)
            | 11 -> (((r9_combreduction ex position),rule_number,position,"r_9") :: l_upl)
            | 12 -> (((r10_combreduction ex position),rule_number,position,"r_{10}") :: l_upl)
            | 13 -> (((r11_combreduction ex position),rule_number,position,"r_{11}") :: l_upl)
  	    | 14 -> (((eta_combreduction ex position),rule_number,position,"Eta") :: l_upl)
            | 15 -> (List.append (left_norm_suscomb ex position) l_upl)
            | 16 -> (List.append (ran_normal_suscomb (betasreductioncomb ex position) position) l_upl)  
	    | _ -> assert false 
and
  left_norm_suscomb expinit pos = 
  let l_upl = ref [(expinit,1,pos,"\\beta_s")] in 
  let exp = ref (betasreductioncomb expinit pos) in 
  let posit = ref ([]:int list) in
    while (left_red_suscomb !exp []) <> ([],0) do
      posit := Pervasives.fst(left_red_suscomb !exp []);
      l_upl := reduce_suscomb !exp (Pervasives.snd(left_red_suscomb !exp [])) !posit !l_upl;
      exp := (Common.first(List.hd !l_upl))
    done;
    !l_upl
                
(** This is the main loop for the suspension calculus. *)
let rec lsuspcomb f =
  try
    let init_exp = Input.ask_exp Selexersuscomb.convertStr2Exp_suscomb in
    let i_upl = [((Selexersuscomb.convertStr2Exp_suscomb init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = lst_suscomb c_exp in
        print_newline();
        print_string "Expression: ";
        print_exp_suscomb c_exp;
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
                    let c_upl = reduce_suscomb c_exp r_num position l_upl in
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
                | 17 -> Output.print_in_latex "suspcombrules" 4;
                        internal_loop l_upl
	        | 18 -> 
                    internal_loop (List.tl l_upl)
	        | 19 ->
		    print_newline();
		    Output.print_history (List.rev l_upl) print_exp_suscomb; 
		    Input.get_line ();       
		    internal_loop l_upl
	        | 20 -> 
		    Output.latex_output l_upl;
		    internal_loop l_upl
	        | 21 -> 
                    Output.save_red l_upl init_exp 4;
                    internal_loop l_upl
	        | 22 -> 
		    Output.ask_save l_upl init_exp 4;
		    internal_loop i_upl
	        | 23 -> 
		    Output.ask_save l_upl init_exp 4;
		    f()
	        | 24 -> 
		    Output.ask_save l_upl init_exp 4;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  
