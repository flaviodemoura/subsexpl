(**********************************************************)
(*                       SUBSEXPL                         *)
(* Step by step simulation of the reduction in explicit   *)
(* substitution calculi:  suspension calculus, lambda s_e *)
(* calculus and lambda sigma calculus                     *)
(*                                                        *)
(* Grupo de Teoria da Computacao,                         *)
(* Departamento de Matematica, Universidade de Brasilia   *)
(* ULTRA group,                                           *)
(* School of MACS, Heriot-Watt University                 *)
(* Authors: Flavio L. C. de Moura, Mauricio Ayala-Rincon  *) 
(*          and F. Kamareddine.                           *)
(*                                                        *)
(* Permission to copy and reuse this file mantaining its  *)
(* procedence indicated above                             *)
(**********************************************************)

(** This module contains the main loop for the lambda sigma calculus. 
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes
open Sematchls
open Seredls

(** print a lambda sigma expression. *)
let rec print_exp_ls exp = 
  match exp with 
    | Dummy -> print_string "\\diamondsuit" 
    | One -> print_string "1"
    | Vr c -> 
	print_string "Vr ";
	print_string c
    | A(e1,e2) ->    
	print_string "(";
	print_exp_ls e1;
	print_string "  ";
	print_exp_ls e2;
	print_string ")"
    | L(e1,_,_) -> 
	print_string "\\lambda(";
	print_exp_ls e1;
	print_string ")"
    | Sb(e1,sb) -> 
	print_string " ";
	print_exp_ls e1;
	print_string "[";
	print_subs sb;
	print_string "]"
    | _ -> assert false
and 
  print_subs subs = 
  match subs with
    | Id -> print_string " Id"
    | Up -> print_string "\\uparrow"
    | Pt(e1,sb) -> 
	print_string "(";
        print_exp_ls e1;
        print_string ".";
        print_subs sb;
        print_string ")"
   | Cp(s1,s2) -> 
	print_string "(";
        print_subs s1;
        print_string "\\textdegree";
        print_subs s2;
        print_string ")"

(** This function takes an expression exp as argument and generates a list of pairs of the form (rule name, positions where this rule apply). *)
let lst_ls exp = 
  [
    ("Beta: ",(matchingBeta1 exp [] []));
    ("App: ",(matchingApp exp [] []));
    ("Abs: ",(matchingAbs exp [] []));
    ("Clos: ",(matchingClos exp [] []));
    ("VarCons: ",(matchingVarCons exp [] []));
    ("Id: ",(matchingId exp [] []));
    ("Assoc: ",(matchingAssoc exp [] []));
    ("Map: ",(matchingMap exp [] []));
    ("IdL: ",(matchingIdL exp [] []));
    ("IdR: ",(matchingIdR exp [] []));
    ("ShiftCons: ",(matchingShiftCons exp [] []));
    ("VarShift: ",(matchingVarShift exp [] []));
    ("SCons: ",(matchingSCons exp [] []));
    ("Eta: ",(matchingEta exp [] []));
    ("One beta full step (leftmost): ",(matchingBeta1 exp [] []));
    ("One beta full step (random): ",(matchingBeta1 exp [] []));
    ("Lambda sigma rules (dvi).", [])
  ]
    
(** This is an auxiliary function used by the normalisation function. *)
let lredices1 exp =
  if ( ((matchingAbs exp [] []) <> [])       or 
       ((matchingClos exp [] []) <> [])      or
       ((matchingVarCons exp [] []) <> [])   or
       ((matchingId exp [] []) <> [])        or
       ((matchingAssoc exp [] []) <> [])     or
       ((matchingMap exp [] []) <> [])       or
       ((matchingIdL exp [] []) <> [])       or
       ((matchingIdR exp [] []) <> [])       or
       ((matchingShiftCons exp [] []) <> []) or
       ((matchingVarShift exp [] []) <> [])  or
       ((matchingSCons exp [] []) <> [])     or
       ((matchingApp exp [] []) <> []) ) then true else false
    
(** This is the 'random' normalisation function. *)
let ran_normal_ls expinit pos =
  let l_upl = ref [(expinit,1,pos,"Beta")] in
  let exp = ref expinit in 
  let posit = ref [0] in
    while (lredices1 !exp) do 
      while (matchingApp !exp [] []) <> [] do
        posit := (List.hd(matchingApp !exp [] []));
	exp := (appreduction !exp !posit);
	l_upl := ((!exp,2,!posit,"App") :: !l_upl)
      done;!exp;
      while (matchingAbs !exp [] []) <> [] do
        posit := (List.hd (matchingAbs !exp [] []));
	exp := (absreduction !exp !posit);
	l_upl := (!exp,3,!posit,"Abs") :: !l_upl
      done;!exp; 
      while (matchingClos !exp [] []) <> [] do
        posit := (List.hd (matchingClos !exp [] []));
	exp := (closreduction !exp !posit);
	l_upl := (!exp,4,!posit,"Clos") :: !l_upl
      done;!exp;
      while (matchingVarCons !exp [] []) <> [] do
        posit := (List.hd (matchingVarCons !exp [] []));
	exp := (varconsreduction !exp !posit);
	l_upl := (!exp,5,!posit,"VarsCons") :: !l_upl
      done;!exp;
      while (matchingId !exp [] []) <> [] do
        posit := (List.hd (matchingId !exp [] []));
	exp := (idreduction !exp !posit);
	l_upl := (!exp,6,!posit,"Id") :: !l_upl
      done;!exp;
      while (matchingAssoc !exp [] []) <> [] do
        posit := (List.hd (matchingAssoc !exp [] []));
	exp := (assocreduction !exp !posit);
	l_upl := (!exp,7,!posit,"Assoc") :: !l_upl
      done;!exp;
      while (matchingMap !exp [] []) <> [] do
        posit := (List.hd (matchingMap !exp [] []));
	exp := (mapreduction !exp !posit);
	l_upl := (!exp,8,!posit,"Map") :: !l_upl
      done;!exp;
      while (matchingIdL !exp [] []) <> [] do
        posit := (List.hd (matchingIdL !exp [] []));
	exp := (idlreduction !exp !posit);
	l_upl := (!exp,9,!posit,"IdL") :: !l_upl
      done;!exp;
      while (matchingIdR !exp [] []) <> [] do
        posit := (List.hd (matchingIdR !exp [] []));
	exp := (idrreduction !exp !posit);
	l_upl := (!exp,10,!posit,"IdR") :: !l_upl
      done;!exp;
      while (matchingShiftCons !exp [] []) <> [] do
        posit := (List.hd (matchingShiftCons !exp [] []));
	exp := (shiftconsreduction !exp !posit);
	l_upl := (!exp,11,!posit,"ShiftCons") :: !l_upl
      done;!exp;
      while (matchingVarShift !exp [] []) <> [] do
        posit := (List.hd (matchingVarShift !exp [] []));
	exp := (varshiftreduction !exp !posit);
	l_upl := (!exp,12,!posit,"VarShift") :: !l_upl
      done;!exp;
      while (matchingSCons !exp [] []) <> [] do
        posit := (List.hd (matchingSCons !exp [] []));
	exp := (sconsreduction !exp !posit);
	l_upl := (!exp,13,!posit,"SCons") :: !l_upl
      done;!exp;
    done;
    !l_upl

(** This function search for the leftmost redex of the given expression [exp] in the lambda sigma calculus. It returns a pair of the form (the leftmost redex of the given expression [exp],the rule number corresponding to this redex). *)
let rec left_red_ls exp pos = 
  match exp with 
    | A(e1,e2) -> 
        let aux = (left_red_ls e1 (List.append pos [1])) in 
          if aux = ([],0) 
          then (left_red_ls e2 (List.append pos [2]))
          else aux
    | L(e,_,_) -> (left_red_ls e (List.append pos [1]))
    | Sb(e,Id) -> (pos,6)
    | Sb(e,sb) -> 
        (match e with
           | A(e1,e2) -> (pos,2)
           | L(e,_,_) -> (pos,3)
           | Sb(e1,sb1) -> (pos,4)
           | One -> (match sb with
                       | Pt(e1,sb1) -> (pos,5)
                       | Id -> (pos,6)
                       | _ -> left_red_ls_subs sb (List.append pos [2]))
           | _ -> (left_red_ls_subs sb (List.append pos [2])))
    | _ -> ([],0)
and
  left_red_ls_subs sub pos = 
  match sub with
    | Cp(s1,Id) -> (pos,10)
    | Cp(s1,s2) ->
        (match s1 with
           | Cp(sb1,sb2) -> (pos,7)
           | Pt(e,sb1) -> (pos,8)
           | Id -> (pos,9)
           | Up -> 
               (match s2 with 
                  | Pt(e,sb1) -> (pos,11)
                  | _ -> left_red_ls_subs s2 (List.append pos [2])))
    | Pt(Sb(One,sb1),Cp(Up,sb2)) ->
        if sb1 = sb2
        then (pos,13)
        else 
          let aux = left_red_ls_subs sb1 (List.append pos [1;2]) in
            if aux = ([],0)
            then left_red_ls_subs sb2 (List.append pos [2;2])
            else aux
    | Pt(e,s1) ->
        (match e with
           | One -> 
               (match s1 with
                  | Up -> (pos,12)
                  | _ -> left_red_ls_subs s1 (List.append pos [2]))
           | _ -> 
               let aux = left_red_ls e (List.append pos [1]) in
                 if aux = ([],0)
                 then left_red_ls_subs s1 (List.append pos [2])
                 else aux)
    | _ -> ([],0)

(** [reduce_ls] takes as argument a lambda sigma expression [ex], an interger [rule_number], an integer list [position] and a list of 4-uples and return a new list of 4-uples which contains a new 4-uple formed by the expression [ex] reduced by the rule corresponding to [rule_number] at position [position]. *)
let rec reduce_ls ex rule_number position l_upl =
	  match rule_number with 
	    | 1 -> (((betareduction1 ex position),rule_number,position,"Beta") :: l_upl)
	    | 2 -> (((appreduction ex position),rule_number,position,"App") :: l_upl)
	    | 3 -> (((absreduction ex position),rule_number,position,"Abs") :: l_upl)
	    | 4 -> (((closreduction ex position),rule_number,position,"Clos") :: l_upl)
	    | 5 -> (((varconsreduction ex position),rule_number,position,"VarCons") :: l_upl)
	    | 6 -> (((idreduction ex position),rule_number,position,"Id") :: l_upl)
	    | 7 -> (((assocreduction ex position),rule_number,position,"Assoc") :: l_upl)
	    | 8 -> (((mapreduction ex position),rule_number,position,"Map") :: l_upl)
	    | 9 -> (((idlreduction ex position),rule_number,position,"IdL") :: l_upl)
	    | 10 -> (((idrreduction ex position),rule_number,position,"IdR") :: l_upl)
	    | 11 -> (((shiftconsreduction ex position),rule_number,position,"ShiftCons") :: l_upl)
	    | 12 -> (((varshiftreduction ex position),rule_number,position,"VarShift") :: l_upl)
	    | 13 -> (((sconsreduction ex position),rule_number,position,"SCons") :: l_upl)
	    | 14 -> (((etareduction ex position),rule_number,position,"Eta") :: l_upl)
	    | 15 -> (List.append (left_norm_ls (betareduction1 ex position) position) l_upl) 
            | 16 -> (List.append (ran_normal_ls (betareduction1 ex position) position) l_upl)
	    | _ -> assert false 
and
  left_norm_ls expinit pos = 
  let l_upl = ref [(expinit,1,pos,"Beta")] in 
  let exp = ref (betareduction1 expinit pos) in 
  let posit = ref ([]:int list) in
    while (left_red_ls !exp []) <> ([],0) do
      posit := Pervasives.fst(left_red_ls !exp []);
      l_upl := reduce_ls !exp (Pervasives.snd(left_red_ls !exp [])) !posit !l_upl;
      exp := (Common.first(List.hd !l_upl))
    done;
    !l_upl

(** This is the main loop for the lambda sigma calculus. *)
let rec lsigma f =
  try
    let init_exp = Input.ask_exp Selexerls.convertStr2Exp_ls in
    let i_upl = [((Selexerls.convertStr2Exp_ls init_exp),0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = lst_ls c_exp in
        print_newline();
        print_string "Expression: ";
        print_exp_ls c_exp;
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
                    let c_upl = reduce_ls c_exp r_num position l_upl in
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
                    Output.print_in_latex "sigmarules" 1;
                    internal_loop l_upl
                | 18 ->
                    internal_loop (List.tl l_upl)
	        | 19 ->
		    print_newline();
		    Output.print_history (List.rev l_upl) print_exp_ls; 
		    Input.get_line ();       
		    internal_loop l_upl
	        | 20 -> 
		    Output.latex_output l_upl;
		    internal_loop l_upl
	        | 21 -> 
                    Output.save_red l_upl init_exp 1;
                    internal_loop l_upl
	        | 22 -> 
		    Output.ask_save l_upl init_exp 1;
		    internal_loop i_upl
	        | 23 -> 
		    Output.ask_save l_upl init_exp 1;
		    f()
	        | 24 -> 
		    Output.ask_save l_upl init_exp 1;
		    raise Quit
	        | _ -> 
                    print_string "Invalid Option!\n"; 
                    internal_loop l_upl
	    end
    in
      (internal_loop i_upl)
  with Quit -> print_string "Good bye!\n"  
