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

(** This module contains functions that generates menus and print expression on the screen.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine *)   

open Setypes 
open Common
   
(************************ Commom Output Functions *****************************)

(** Print the history recorded in the list [trp_list] on the screen,
    and at the end, print the number of steps used in the current
    reduction. *)
let print_history upl_list print_function = 
  let rec printing_history list f =
    (match list with
       | [] -> print_newline ()
       | header :: tail -> 
	   f (first header);
           print_newline ();
           printing_history tail f)
  in
    printing_history upl_list print_function;
    print_string "Number of steps: ";
    print_int ((List.length upl_list)-1);
    print_newline ();
    print_string "Type ENTER"

(** Convert a integer list into a string. *)  
let string_of_int_list lst = 
  if (List.length lst <> 0) 
  then 
    let rec str_of_int_list list = 
      match list with
	| [] -> ""
	| hd::tl -> (string_of_int hd) ^ (str_of_int_list tl) in
      (str_of_int_list lst) 
  else "0"
    
(** Convert a list of positions which are given by [int list list]
    into a list of string. *)
let rec str_of_red int_list_list =
  match int_list_list with
    | [] -> []
    | hd::tl -> (string_of_int_list hd)::(str_of_red tl)

(** Save the current reduction list into a file. *)
let save_red reduc_list exp calc =
  print_string "Save on file: ";
  let file_name = Input.get_line () in
  let output_file_desc = Pervasives.open_out file_name in
  let print_on_file s = Pervasives.output_substring output_file_desc s 0 (String.length s)
  in
  let rec output_reduction = function
    | [] -> ()
    | e::f -> 
	begin
	  print_on_file ((string_of_int(Common.secnd e)) ^ "\n");
	  print_on_file ((string_of_int_list(Common.third e)) ^ "\n"); 
	  output_reduction f
	end
  in
    print_on_file ((string_of_int calc) ^ "\n");
    print_on_file (exp ^ "\n"); 
    output_reduction (List.tl(List.rev reduc_list));
    Pervasives.close_out output_file_desc;
    print_string ("File " ^ file_name ^ " saved.\n")
      
(** Ask for saving or not the current reduction. *)      	
let rec ask_save red_list exp calc =
  print_string "Save current reduction? (y/n) ";
  let answ = Input.get_line () in
    match answ with
      | "y" -> 
	  save_red red_list exp calc;
      | "n" -> ()
      | _ -> 
	  print_string "Please answer y or n.\n"; 
	  ask_save red_list exp calc 
	    
(** Initial screen. *)	    
let fst_menu () = 
  print_string "*************** SUBSEXPL ***************\n";
  print_newline ();
  print_string "SELECT the calculus\n";
  print_string "TYPE \n";
  print_string "      0 for the Pure \lambda-calculus (with names or deBruijn)\n";
  print_string "      1 for the \lambda\sigma-calculus\n";
  print_string "      2 for the \lambda s_e-calculus\n";
  print_string "      3 for the Suspension calculus\n";
  print_string "      4 for the Combining Suspension calculus\n";
  print_string "      5 for the Grammatical description IN/OUT (and internal)\n";
  print_string "OR    6 for quit\n";
  print_string "> "

(** Initial screen. *)      
let new_menu () = 
  print_string "*************** SUBSEXPL ***************\n";
  print_newline ();
  print_string "SELECT the calculus notation\n";
  print_string "TYPE \n";
  print_string "      0 for deBruijn's notation (se)\n";
  print_string "      1 for deBruijn's notation (susp)\n";
  print_string "      2 for usual notation with names (se)\n";
  print_string "      3 for usual notation with names (susp)\n";
  print_string "      4 for grammatical description of deBruijn's notation\n";
  print_string "      5 for grammatical description of named notation\n";
  print_string "OR    6 for quit\n";
  print_string "> "

(** Display the menu for the chosen calculus. *)
let display_opt_menu l =
  let item = ref 1 in
  let print_item s =
    print_string((string_of_int !item)^". " ^ s) in
  let rec print_positions = function 
    | [] -> ()
    | p::t ->
        print_string (string_of_int_list p);
        print_string " ";
        print_positions t in
  let print_end_of_item () =
    print_string "\n" in
  let rec print_calculus_items = function
    | [] -> ()
    | (name,positions)::t ->
        print_item name;
        print_positions positions;
        print_end_of_item ();
        item:= !item+1;
        print_calculus_items t
  in
  let rec print_generic_items = function
    | [] -> ()
    | s::t ->
        print_item s;
        print_string ".";
        print_end_of_item ();
        item:= !item+1;
        print_generic_items t
  in
    print_calculus_items l;
    print_generic_items
      [
        "Back one step";
        "See history";
        "Latex output";
        "Save current reduction";
        "Restart current reduction";
        "Restart SUBSEXPL";
        "Quit"
      ] 
      
let rec isUpgrading sub =
  match sub with 
    | Id -> true
    | Up -> true
    | Cp(Up, sub1) -> (isUpgrading sub1)
    | _ -> false

let rec countUpgrading sub =
match sub with
    | Id -> 0
    | Up -> 1
    | Cp(Up,sub1) -> 1 + countUpgrading sub1
    | _  -> 9999

(** Auxiliary function to generate the latex code. *)    
(** FIXME: look for names here *)
let rec latex_string_of_exp exp pos = 
  match exp with
    | L (e,_,_) -> (match pos with 
		  | [] -> "\\underline{\\SEL{" ^ (latex_string_of_exp e [3]) ^ "}}" 
		  | 1::l -> "\\SEL{" ^ (latex_string_of_exp e l) ^ "}" 
		  | _ ->  "\\SEL{" ^ (latex_string_of_exp e [3]) ^ "}")  
    | A (e1,e2) -> (match pos with
		      | [] -> 
			  "\\underline{\\SEA{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}}" 
		      | 1::l ->
			  "\\SEA{" ^ (latex_string_of_exp e1 l) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}"
		      | 2::l ->
			  "\\SEA{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 l) ^ "}"
		      | _ ->
                          "\\SEA{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}"  )
    | DB (i) -> "\\SEDB{" ^ (string_of_int i) ^ "}" 
    | One -> "\\SEDB{1}" 
    | Vr (s) -> "\\SEVr{" ^ s ^ "}"
    | Sb(One, Id) -> ( match pos with 
                         | [] -> "\\underline{\\SESb{\\SEDB{1}}{\\SEId}}"
                         |  _ -> "\\SEDB{1}")
    | Sb(One, sub) -> (if (isUpgrading(sub)) then "\\SEDB{" ^ (string_of_int (1 + countUpgrading(sub))) ^ "}" 
                         else 
                           (match pos with
			     | [] -> 
                                   "\\underline{\\SESb{\\SEDB{1}}{" ^ (latex_string_of_sub sub [3]) ^ "}}"
                             | 2::l -> 
                                   "\\SEDB{1}{" ^ (latex_string_of_sub sub l) ^ "}"
                             | _ ->   
                                   "\\SEDB{1}{" ^ (latex_string_of_sub sub [3]) ^ "}" ))
(** To define two different options for the lambda sigma: abreviating de Bruijn indice codifications or not **) 
    | Sb (e , sub) ->  (match pos with
			  | [] ->
			      "\\underline{\\SESb{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}}"
			  | 1::l ->
			      "\\SESb{" ^ (latex_string_of_exp e l) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}"
			  | 2::l ->
			      "\\SESb{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub l) ^ "}"
			  | _ ->
			      "\\SESb{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}" )
    | S (i,e1,e2) -> (match pos with
		        | [] ->
			    "\\underline{\\SES{" ^ (string_of_int i) ^ "}{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}}"
		        | 1::l ->
		            "\\SES{" ^ (string_of_int i) ^ "}{" ^ (latex_string_of_exp e1 l) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}"
		        | 2::l ->
			    "\\SES{" ^ (string_of_int i) ^ "}{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 l) ^ "}"
		        | _ ->
			    "\\SES{" ^ (string_of_int i) ^ "}{" ^ (latex_string_of_exp e1 [3]) ^ "}{" ^ (latex_string_of_exp e2 [3]) ^ "}" )
    | P (i1,i2,e) -> (match pos with
		        | [] ->
			    "\\underline{\\SEP{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_exp e [3]) ^ "}}"
		        | 1::l ->
			    "\\SEP{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_exp e l) ^ "}"
		        | _ ->
			    "\\SEP{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_exp e [3]) ^ "}" )
    | Dummy -> "\\SEDummy"
    | Sp (e,i1,i2,env) ->  (match pos with
			      | [] ->
				  "\\underline{\\SESp{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}}"
			      | 1::l ->
				  "\\SESp{" ^ (latex_string_of_exp e l) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}"
			      | 2::l ->  
				  "\\SESp{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env l) ^ "}"
			      | _ ->  
				  "\\SESp{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}" ) 
and latex_string_of_sub subs pos = match subs with
  | Id -> "\\SEId"
  | Up -> "\\SEUp"
  | Pt(e,sub) ->  (match pos with
		     | [] ->
			 "\\underline{\\SEPt{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}}"
		     | 1::l ->
			 "\\SEPt{" ^ (latex_string_of_exp e l) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}"
		     | 2::l ->
			 "\\SEPt{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub l) ^ "}"
		     | _ ->
			 "\\SEPt{" ^ (latex_string_of_exp e [3]) ^ "}{" ^ (latex_string_of_sub sub [3]) ^ "}" )
  | Cp(sub1,sub2) -> (match pos with
			| [] ->
			    "\\underline{\\SECp{" ^ (latex_string_of_sub sub1 [3]) ^ "}{" ^ (latex_string_of_sub sub2 [3]) ^ "}}"
			| 1::l ->
			    "\\SECp{" ^ (latex_string_of_sub sub1 l) ^ "}{" ^ (latex_string_of_sub sub2 [3]) ^ "}"
			| 2::l ->
			    "\\SECp{" ^ (latex_string_of_sub sub1 [3]) ^ "}{" ^ (latex_string_of_sub sub2 l) ^ "}"
			| _ ->
			    "\\SECp{" ^ (latex_string_of_sub sub1 [3]) ^ "}{" ^ (latex_string_of_sub sub2 [3]) ^ "}" )
and latex_string_of_env envr pos = match envr with
  | Con (env_term, env) -> (match pos with 
                               | 1::l -> "\\SECon{" ^ (latex_string_of_envterm env_term l) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}"
                               | 2::l -> "\\SECon{" ^ (latex_string_of_envterm env_term [3]) ^ "}{" ^ (latex_string_of_env env l) ^ "}"
                               | _ -> "\\SECon{" ^ (latex_string_of_envterm env_term [3]) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}"  )
  | Ck (env1,i1,i2,env2) ->  (match pos with
				| [] ->
				    "\\underline{\\SECk{" ^ (latex_string_of_env env1 [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env2 [3]) ^ "}}" 
				| 1::l ->
				    "\\SECk{" ^ (latex_string_of_env env1 l) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env2 [3]) ^ "}"
				| 2::l ->
				    "\\SECk{" ^ (latex_string_of_env env1 [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env2 l) ^ "}"
				| _ ->
				    "\\SECk{" ^ (latex_string_of_env env1 [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env2 [3]) ^ "}" )
  | Nilen -> "\\SENil"
and latex_string_of_envterm envrterm pos = match envrterm with
  | Paar (e,i) ->  (match pos with
                     | 1::l -> "\\SEPaar{" ^ (latex_string_of_exp e l)^ "}{" ^ (string_of_int i) ^ "}"
                     | _ ->  "\\SEPaar{" ^ (latex_string_of_exp e [3])^ "}{" ^ (string_of_int i) ^ "}" )
  | Ar (i) -> "\\SEAr{" ^ (string_of_int i) ^ "}"
  | LG (env_term,i1,i2,env) -> (match pos with
				  | [] ->
				      "\\underline{\\SELG{" ^ (latex_string_of_envterm env_term [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}}"
				  | 1::l ->
				      "\\SELG{" ^ (latex_string_of_envterm env_term l) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}"
				  | 2::l ->
				      "\\SELG{" ^ (latex_string_of_envterm env_term [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env l) ^ "}"
				  | _ ->
				      "\\SELG{" ^ (latex_string_of_envterm env_term [3]) ^ "}{" ^ (string_of_int i1) ^ "}{" ^ (string_of_int i2) ^ "}{" ^ (latex_string_of_env env [3]) ^ "}" )
      
(** Function that print the latex code into a file, compile it and launch xdvi. *)    
let print_history_in_latex output_file_name exp_list =
  let output_file_desc =
    Unix.openfile output_file_name
      [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL]
      438
  in
  let print_on_file s =
    let _ = Unix.write_substring output_file_desc s 0 (String.length s)
    in ()
  in
  let rec output_history = function
      [] -> ()
    | [e] -> print_on_file ( "$" ^ (latex_string_of_exp (Common.first e) [3]) ^ "$ \\\ \n")
    | e::f::l -> 
	print_on_file ( "$" ^ (latex_string_of_exp (Common.first e) (Common.third f) ) ^ "\\rightarrow_{"^(Common.fourth f)^"}" ^ "$\\\ \n");
	output_history (f::l)
  in
    print_on_file("\\documentclass{article}
\\usepackage{fullpage,amsmath,amsfonts}
\\newcommand{\\SEL}[1]{(\\lambda #1)}
\\newcommand{\\SEA}[2]{(#1\\;#2)}
\\newcommand{\\SEDB}[1]{{\\tt \\underline{#1}}}
\\newcommand{\\SEVr}[1]{#1}
\\newcommand{\\SESb}[2]{#1[#2]}
\\newcommand{\\SES}[3]{(#2\\sigma^{#1}#3)}
\\newcommand{\\SEP}[3]{\\varphi^{#1}_{#2}(#3)}
\\newcommand{\\SEDummy}{\\diammond}
\\newcommand{\\SESp}[4]{[\\![#1,#2,#3,#4]\\!]}
\\newcommand{\\SEId}{id}
\\newcommand{\\SEUp}{\\uparrow}
\\newcommand{\\SEPt}[2]{(#1\\cdot #2)}
\\newcommand{\\SECp}[2]{(#1\\circ#2)}
\\newcommand{\\SECon}[2]{#1::#2}
\\newcommand{\\SECk}[4]{\\{\\!\\{#1,#2,#3,#4\\}\\!\\}}
\\newcommand{\\SENil}{nil}
\\newcommand{\\SEPaar}[2]{(#1,#2)}
\\newcommand{\\SEAr}[1]{@#1}
\\newcommand{\\SELG}[4]{\\langle\\!\\langle#1,#2,#3,#4\\rangle\\!\\rangle}

\\begin{document}\\footnotesize\\noindent \n");
    output_history exp_list;
    print_on_file ("\\\ Number of steps: ");
    print_on_file (string_of_int ((List.length exp_list)-1));
    print_on_file ("\\end{document}");
    Unix.close output_file_desc
    (* Unix.system ("latex " ^ output_file_name);   *)
    (* Unix.system ("xdvi " ^ output_file_name ^" & ") *)

(** Function that generates the dvi file with the rewriting rules of
    the selected calculus. Requires xdvi installed. *)
let print_in_latex () arg =
  Unix.system ("latex "^ arg);
  Unix.system ("xdvi "^ arg ^" &")
    
(** Generate the latex code into a file. *)
let rec latex_output l_trp =
  print_endline "Latex output on file :";
  let output_file_name = Input.get_line () in
    try
      print_history_in_latex output_file_name (List.rev l_trp);
      print_endline "Done. Type ENTER";
      Input.get_line()
    with
	Unix.Unix_error(_) ->
	  print_endline "File exists already.";
	  latex_output l_trp

(** Print the input grammar on the screen. *)
let lgrammar () =
  begin
    print_newline ();
    print_string "Input grammatical description\n";
    print_string "-----------------------------\n";
    print_newline ();
    print_string "Operators used in all calculi:\n";
    print_string "Lambda ::= L( _ )\n";
    print_string "Application ::= A( _ , _ )\n";
    print_string "de Bruijn indices ::= integers\n";
    print_newline ();
    print_string "Lambda s_e operators:\n";
    print_string "---------------------\n";
    print_string "Sigma operator ::= S(superscript, _ , _ )\n";
    print_string "Phi operator ::= P(superscript,subscript, _ )\n";
    print_newline ();
    print_string "Lambda sigma operators:\n";
    print_string "-----------------------\n";
    print_string "Lambda ::= L( _ )\n";
    print_string "Application ::= A( _ , _ )\n";
    print_string "Substitution composition ::= Cp( _ , _ )\n";
    print_string "Substitution application ::= Sb( _ , _ )\n";
    print_string "Uparrow  ::= Up\n";
    print_string "Dot  ::= Pt( _ , _ )\n";
    print_newline ();
    print_string "Suspension operator:\n";
    print_string "--------------------\n";
    print_string "Suspension term: Sp(exp,i,j,env)\n";
    print_string "For other operators, see documentation distributed with the source code.\n";
    print_newline ();
    print_string "Example (valid for all calculi):  A(L(L(2)),5)\n";
    print_newline ();
    print_string "Type ENTER";
    Input.get_line ();
  end


(** Print the input grammar on the screen. *)
let new_grammar() =
  begin
    print_newline();
    print_string "Input grammatical description in BNF & Regex\n";
    print_string "-----------------------------\n";
    print_newline();
    print_string "Operators used in all calculi:\n";
    print_string "Term        ::= identifier | Application | Lambda | (Term)\n";
    print_string "identifier  ::= [A-Za-z][A-Za-z0-9_]*\n";
    print_string "Lambda      ::= \ identifier (, identifier)* . Term\n";
    print_string "Application ::= Term Term\n";
    print_newline();
    print_string "Applications are associated to the left. e.g: M N P Q \equal (((M N) P) Q)\n";
    print_newline();
    print_string "Type ENTER";
    Input.get_line ();
  end


(** Function that prints the latex code into a file containing the
rewriting system of the selected calculus, compiles it and launches
the generated dvi file. *)
let print_in_latex output_file_name op =
  let output_file_desc =
    Unix.openfile output_file_name
      [Unix.O_TRUNC; Unix.O_RDWR; Unix.O_CREAT]
      438
  in
  let print_on_file s =
    let _ = Unix.write_substring output_file_desc s 0 (String.length s)
    in ()
  in
  let rec output_rules = 
    match op with
      | 1 -> 
          print_on_file(
            "\\documentclass[12pt]{article}\n"^
              "\\newcommand{\\db}[1]{{\\bf \\underline{#1}}}\n"^
              "\\title{The $\\lambda\\sigma$-rewriting system}\n"^
              "\\date{\\empty}\n"^
              "\\begin{document}\n"^
              "\\maketitle\n"^
              "The syntax of the $\\lambda\\sigma$-calculus is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\\mbox{\\bf Terms} &  a,b & ::=  & \\db{1}\\;|\\; X\\;|\\; (a\\;b)\\;|\\;\\lambda.a\\;|\\; a[s]  \\\ \n"^
              "\\mbox{\\bf Substitutions} \\hspace{0.2in} & s,s' & ::= & {\\it id}\\;|\\;\\uparrow\\;|\\;a\\cdot s\\;|\\;s\\circ s'\n"^
              "\\end{array}$$\n\n"^
              "The corresponding syntax in the language of SUBEXPL is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\\mbox{\\bf Terms} &  {\\tt a, b} & ::=  & {\\tt One}\\;|\\; {\\tt Var\\; x}\\;|\\; {\\tt A(a,b)}\\;|\\;{\\tt L(a)}\\;|\\; {\\tt Sb(a,s)} \\\ \n"^
              "\\mbox{\\bf Substitutions} \\hspace{0.2in} \\hspace{0.5in} & {\\tt s, s'} & ::= & {\\tt Id}\\;|\\;{\\tt Up}\\;|\\;{\\tt Pt(a,s)}\\;|\\;{\\tt Cp(s,s')}\n"^
              "\\end{array}$$\n\n"^
              "The $\\lambda\\sigma$-rewriting system is given by:\n\n"^
              "\\begin{center}\n"^
              "\\begin{tabbing}\n"^
              "\\(\\ \\) (r11)\\quad\\=\\qquad\\qquad\\=\\kill\n"^
              "\\(\\ \\) (Beta)\\> \\> $(\\lambda.M) \\; N \\rightarrow M[N.id]$\\\[2mm]\n"^
              "\\(\\ \\) (App)\\> \\> $(M \\; N)[s] \\rightarrow (M[s] \\; N[s])$\\\[2mm]\n"^
              "\\(\\ \\) (Abs)\\> \\> $(\\lambda.M)[s] \\rightarrow \\lambda.M[\\db{1}.(s\\circ \\uparrow)]$\\\[2mm]\n"^
              "\\(\\ \\) (Clos)\\> \\> $M[s][t] \\rightarrow M[s\\circ t]$\\\[2mm]\n"^
              "\\(\\ \\) (VarCons)\\> \\> $\\db{1}[M.s] \\rightarrow M$\\\[2mm]\n"^
              "\(\ \) (Id)\> \> $M[id] \\rightarrow M$\\\[2mm]\n"^
              "\(\ \) (Assoc)\> \> $(s_1 \circ s_2) \circ t \\rightarrow s_1 \circ (s_2 \circ t)$\\\[2mm]\n"^
              "\(\ \) (Map)\> \> $(M.s)\circ t \\rightarrow M[t].(s \circ t)$\\\[2mm]\n"^
              "\(\ \) (IdL)\> \> $id \circ s \\rightarrow s$\\\[2mm]\n"^
              "\(\ \) (IdR)\> \> $s \circ id \\rightarrow s$\\\[2mm]\n"^
              "\(\ \) (ShiftCons)\>  \>$\uparrow \circ (M.s) \\rightarrow s$\\\[2mm]\n"^
              "\(\ \) (VarShift)\> \> $\db{1}.\uparrow \\rightarrow id$\\\[2mm]\n"^
              "\(\ \) (SCons)\> \> $\db{1}.[s](\uparrow \circ s) \\rightarrow s$\\\[2mm]\n"^
              "\(\ \) (Eta)\> \> $\lambda(M \; \db{1}) \\rightarrow N$ se $M =_{\sigma} N[\uparrow]$ \n"^
              "\end{tabbing}\n"^
              "\end{center}\n\n"^
              "\end{document}"
          )
      | 2 ->
          print_on_file(
            "\documentclass[12pt]{article}\n"^
              "\\newcommand{\db}[1]{{\\bf \underline{#1}}}\n"^
              "\\title{The $\lambda s_e$-rewriting system}\n"^
              "\date{\empty}\n"^
              "\\begin{document}\n"^
              "\maketitle\n"^
              "The syntax of the $\lambda s_e$-calculus is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  a,b & ::=  & \db{n}\;|\; X\;|\; (a\;b)\;|\;\lambda.a\;|\; \varphi^i_k a \;|\; a\sigma^i b \mbox{ where }k\geq 0 \mbox{ and } n,i\geq 1.\n"^
              "\end{array}$$\n"^
              "The corresponding syntax in the language of SUBEXPL is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  {\\tt a, b} & ::=  & {\\tt n}\;|\; {\\tt Var\; x}\;|\; {\\tt A(a,b)}\;|\;{\\tt L(a)}\;|\; {\\tt P(i,k,a)} \;|\; {\\tt S(i,a,b)}\n"^
              "\end{array}$$\n"^
              "The $\lambda s_e$-rewriting system is given by:\n"^
              "\\begin{center}\n"^
              "\\begin{tabbing}\n"^
              "\(\ \) (r11)\quad\=\qquad\qquad\qquad\=\kill\n"^
              "\(\ \) ($\sigma$-generation)\> \> $(\lambda.M) \; N \\rightarrow M \; \sigma^1 \; N$\\\[2mm]\n"^
              "\(\ \) ($\sigma$-$\lambda$-transition)\> \> $(\lambda.M) \; \sigma^i \; N \\rightarrow \lambda.(M \; \sigma^{i+1} \; N) $\\\[2mm]\n"^
              "\(\ \) ($\sigma$-app-transition)\> \> $(M_1 \; M_2) \; \sigma^i \; N \\rightarrow ((M_1 \; \sigma^i \; N)(M_2 \; \sigma^i \; N)) $\\\[2mm]\n"^
              "\(\ \) ($\sigma$-destruction)\> \> $\db{n} \sigma^i N \\rightarrow\n"^
              "\left \{\\begin{array}{lr}\n"^
              "\db{n-1} & \mbox{{\\rm if $n>i$}} \\\ \n"^
	      "\varphi_0^i N & \mbox{{\\rm if $n=i$}} \\\ \n"^
              "\db{n} & \mbox{{\\rm if $n<i$}}\n"^
  	      "\end{array} \\right.$\\\[2mm]\n"^
              "\(\ \) ($\varphi$-$\lambda$-transition)\> \> $\varphi_k^i (\lambda.M) \\rightarrow \lambda.(\varphi_{k+1}^i M)$\\\[2mm]\n"^
              "\(\ \) ($\varphi$-app-transition)\> \> $\varphi_k^i(M_1 \; M_2) \\rightarrow ((\varphi_k^i M_1) \; (\varphi_k^i M_2)) $\\\[2mm]\n"^
              "\(\ \) ($\varphi$-destruction)\> \> $\varphi_k^i \db{n} \\rightarrow \left \{\n"^ 
              "\\begin{array}{lr}\n"^
	      "\db{n+i-1} & \mbox{{\\rm if $n>k$}} \\\ \n"^
              "\db{n} & \mbox{{\\rm if $n\leq k$}}\n"^
              "\end{array} \\right. $\\\[2mm]\n"^
              "\(\ \) ($\sigma$-$\sigma$-transition)\> \> $(M_1 \; \sigma^i \; M_2) \sigma^j N \\rightarrow (M_1 \; \sigma^{j+1} \; N) \sigma^i (M_2 \; \sigma^{j-i+1} \; N) $ if $i \leq j$\\\[2mm]\n"^
              "\(\ \) ($\sigma$-$\varphi$-transition 1)\> \> $(\varphi_k^i M) \sigma^j N \\rightarrow \varphi_k^{i-1} M $ if $k < j < k+i $\\\[2mm]\n"^
              "\(\ \) ($\sigma$-$\varphi$-transition 2)\> \> $(\varphi_k^i M) \sigma^j N \\rightarrow \varphi_k^i (M \sigma^{j-i+1} N) $ if $k+i \leq j $\\\[2mm]\n"^
              "\(\ \) ($\varphi$-$\sigma$-transition)\> \> $\varphi_k^i (M \sigma^j N) \\rightarrow (\varphi_{k+1}^i M) \sigma^j(\varphi_{k+1-j}^i N) $ if $j \leq k+1 $\\\[2mm]\n"^
              "\(\ \) ($\varphi$-$\varphi$-transition 1)\> \> $\varphi_k^i (\varphi_l^j M) \\rightarrow \varphi_l^j (\varphi_{k+1-j}^i M)$ if $l+j \leq k $\\\[2mm]\n"^
              "\(\ \) ($\varphi$-$\varphi$-transition 2)\> \> $\varphi_k^i (\varphi_l^j M) \\rightarrow \varphi_l^{j+i-1} M$ if $l\leq k < l+j $\\\[2mm]\n"^
              "\(\ \) (Eta)\> \> $\lambda.(M \; \db{1}) \\rightarrow N$ if $M =_{s_e} \varphi_0^2 N$\n"^
              "\end{tabbing}\n"^
              "\end{center}\n"^
              "\end{document}"
          )
      | 3 ->
          print_on_file(
            "\documentclass[12pt]{article}\n"^
              "\\newcommand{\db}[1]{{\\bf \underline{#1}}}\n"^
              "\\newcommand{\dum}[1]{@ #1}\n"^
              "\\newcommand{\lenv}{{\lbrack\!\lbrack}}\n"^
              "\\newcommand{\\renv}{{\\rbrack\!\\rbrack}}\n"^
              "\\newcommand{\env}[1]{{\lenv #1 \\renv}}\n"^
              "\\newcommand{\lmenv}{{\lbrace\!\!\lbrace}}\n"^
              "\\newcommand{\\rmenv}{{\\rbrace\!\!\\rbrace}}\n"^
              "\\newcommand{\lmenvt}{{\langle\!\langle}}\n"^
              "\\newcommand{\\rmenvt}{{\\rangle\!\\rangle}}\n"^
              "\\newcommand{\monussign}{{\stackrel{.}{\;\overline{\,\,\,}\;}}}\n"^
              "\\newcommand{\monus}[2]{{#1 \monussign #2}}\n"^
              "\\title{The Rewriting System of the Suspension Calculus}\n"^
              "\date{\empty}\n"^
              "\\begin{document}\n"^
              "\maketitle\n"^
              "The syntax of the suspension calculus is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  a,b & ::=  & \db{n}\;|\; X\;|\; (a\;b)\;|\;\lambda.a\;|\; [\![a,i,j,e_1]\!]  \\\ \n"^
              "\mbox{\\bf Environments} \hspace{0.2in} & e_1,e_2 & ::= & {\it nil}\;|\;et::e_1\;|\;\{\!\{e_1,i,j,e_2\}\!\}\\\ \n"^
              "\mbox{\\bf Environments Terms} \hspace{0.2in} & et & ::= & @i\;|\;(a,i)\;|\;\langle\!\langle et,i,j,e_1\\rangle\!\\rangle\n"^
              "\end{array}$$\n"^
              "The corresponding syntax in the language of SUBEXPL is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  {\\tt a, b} & ::=  & {\\tt n}\;|\; {\\tt Var\; x}\;|\; {\\tt A(a,b)}\;|\;{\\tt L(a)}\;|\; {\\tt Sp(a,i,j,e1)} \\\ \n"^
              "\mbox{\\bf Environments} \hspace{0.2in} & {\\tt e1,e2} & ::= & {\\tt Nilen}\;|\;{\\tt Con(et,e1)}\;|\;{\\tt Ck(e1,i,j,e2)}\\\ \n"^
              "\mbox{\\bf Environments Terms} \hspace{0.2in} & {\\tt et} & ::= & {\\tt Ar(i)}\;|\;{\\tt Paar(a,i)}\;|\;{\\tt LG(et,i,j,e_1)}\n"^
              "\end{array}$$\n"^
              "The rewriting system of the suspension calculus is given by:\n"^
              "\\begin{center}\n"^
              "\\begin{tabbing}\n"^
              "\(\ \) (r11)\quad\=\kill\n"^
              "\(\ \) (\(\\beta_s\))\> \(((\lambda.t_1)\; t_2) \\rightarrow \env{t_1, 1,0, (t_2,0) :: nil}\)\\\[2mm]\n"^
              "\(\ \) (r1)\> \(\env{c,ol,nl,e} \\rightarrow c\), where \(c\) is a constant\@.\\\[2mm]\n"^
              "\(\ \) (r2)\>\(\env{\db{i},0,nl,nil} \\rightarrow\db{i + nl}\)\@.\\\[2mm]\n"^
              "\(\ \) (r3)\>\(\env{\db{1},ol,nl, \dum{l} :: e} \\rightarrow\db{nl - l}\)\@.\\\[2mm]\n"^
              "\(\ \) (r4)\> \(\env{\db{1},ol,nl,(t,l) :: e} \\rightarrow\env{t,0,(nl - l),nil}\)\@.\\\[2mm]\n"^
              "\(\ \) (r5)\> \(\env{\db{i}, ol, nl, et :: e} \\rightarrow\env{\db{i - 1},(ol - 1),nl,e},\) for \(i > 1\)\@.\\\[2mm]\n"^
              "\(\ \) (r6)\> \(\env{(t_1\; t_2),ol,nl,e} \\rightarrow(\env{t_1,ol,nl,e}\;\env{t_2,ol,nl,e})\)\@.\\\[2mm]\n"^
              "\(\ \) (r7)\>\(\env{(\lambda.t), ol, nl, e} \\rightarrow(\lambda.\env{t,(ol + 1), (nl + 1), \dum{nl} :: e})\)\@.\\\[2mm]\n"^
              "\(\ \) (Eta)\> \(\lambda.(t_1 \;\db{1}) \\rightarrow t_2 \), \hspace{.1in} if \hspace{.05in}  \(t_1 =_{rm} \env{t_2, 0, 1, nil}.\) \\\[2mm]\n"^
              "\(\ \) (m1)\> \(\env{\env{t,ol_1,nl_1,e_1},ol_2,nl_2,e_2} \\rightarrow \env{t,ol',nl', \lmenv e_1,nl_1,ol_2,e_2 \\rmenv}\),\\\ \>where \(ol' = ol_1 + (\monus{ol_2}{nl_1})\) and \(nl' = nl_2 + (\monus{nl_1}{ol_2})\)\@.\\\[2mm]\n"^
              "\(\ \) (m2)\>\(\lmenv nil, nl, 0, nil \\rmenv \\rightarrow nil\)\@.\\\[2mm]\n"^
              "\(\ \) (m3)\>\(\lmenv nil, nl, ol, et :: e \\rmenv \\rightarrow\lmenv nil,(nl - 1), (ol - 1), e \\rmenv\), for \(nl,ol \geq 1\)\@. \\\[2mm]\n"^
              "\(\ \) (m4)\> \(\lmenv nil, 0, ol, e \\rmenv \\rightarrow e\)\@.\\\[2mm]\n"^
              "\(\ \) (m5)\> \(\lmenv et :: e_1, nl,ol,e_2 \\rmenv \\rightarrow\lmenvt et,nl,ol,e_2 \\rmenvt :: \lmenv e_1,nl,ol,e_2 \\rmenv\)\@.\\\[2mm]\n"^
              "\(\ \) (m6)\> \(\lmenvt et,nl,0,nil \\rmenvt \\rightarrow et\)\@.\\\[2mm]\n"^
              "\(\ \) (m7)\>\(\lmenvt \dum{m}, nl, ol, \dum{l} :: e \\rmenvt \\rightarrow \dum{(l + (\monus{nl}{ol}))}\), for \(nl = m + 1\)\@.\\\[2mm]\n"^
              "\(\ \) (m8)\>\(\lmenvt \dum{m},nl,ol,(t,l) :: e \\rmenvt \\rightarrow(t,(l + (\monus{nl}{ol})))\), for \(nl = m + 1\)\@.\\\[2mm]\n"^
              "\(\ \) (m9)\>\(\lmenvt (t,nl),nl,ol,et :: e \\rmenvt \\rightarrow(\env{t,ol,l',et :: e}, m)\),\\\ \>where \(l' = ind(et)\) and \(m = l' + (\monus{nl}{ol})\)\@.\\\[2mm]\n"^
              "\(\ \) (m10) \>\(\lmenvt et,nl,ol,et' :: e \\rmenvt \\rightarrow\lmenvt et, (nl - 1), (ol - 1), e \\rmenvt,\) for \(nl \\neq ind(et)\)\@.\n"^
	      "\end{tabbing}\n"^
	      "\end{center}\n"^
	      "\end{document}\n"
          )
      | 4 ->
          print_on_file(
            "\documentclass[10pt]{article}\n"^
              "\\newcommand{\db}[1]{{\\bf \underline{#1}}}\n"^
              "\\newcommand{\dum}[1]{@ #1}\n"^
              "\\newcommand{\lenv}{{\lbrack\!\lbrack}}\n"^
              "\\newcommand{\\renv}{{\\rbrack\!\\rbrack}}\n"^
              "\\newcommand{\env}[1]{{\lenv #1 \\renv}}\n"^
              "\\newcommand{\lmenv}{{\lbrace\!\!\lbrace}}\n"^
              "\\newcommand{\\rmenv}{{\\rbrace\!\!\\rbrace}}\n"^
              "\\newcommand{\lmenvt}{{\langle\!\langle}}\n"^
              "\\newcommand{\\rmenvt}{{\\rangle\!\\rangle}}\n"^
              "\\newcommand{\monussign}{{\stackrel{.}{\;\overline{\,\,\,}\;}}}\n"^
              "\\newcommand{\monus}[2]{{#1 \monussign #2}}\n"^
              "\\title{The Rewriting System of the Combining Suspension Calculus}\n"^
              "\date{\empty}\n"^
              "\\begin{document}\n"^
              "\maketitle\n"^
              "\enlargethispage{2cm}\n"^
              "The syntax of the combining suspension calculus is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  a,b & ::=  & \db{n}\;|\; X\;|\; (a\;b)\;|\;\lambda.a\;|\; [\![a,i,j,e_1]\!]  \\\ \n"^
              "\mbox{\\bf Environments} \hspace{0.2in} & e_1,e_2 & ::= & {\it nil}\;|\;et::e_1\\\ \n"^
              "\mbox{\\bf Environments Terms} \hspace{0.2in} & et & ::= & @i\;|\;(a,i)\n"^
              "\end{array}$$\n"^
              "The corresponding syntax in the language of SUBEXPL is given by:\n"^
              "$$\\begin{array}{llcl}\n"^
              "\mbox{\\bf Terms} &  {\\tt a, b} & ::=  & {\\tt n}\;|\; {\\tt Var\; x}\;|\; {\\tt A(a,b)}\;|\;{\\tt L(a)}\;|\; {\\tt Sp(a,i,j,e1)} \\\ \n"^
              "\mbox{\\bf Environments} \hspace{0.2in} & {\\tt e1,e2} & ::= & {\\tt Nilen}\;|\;{\\tt Con(et,e1)}\\\ \n"^
              "\mbox{\\bf Environments Terms} \hspace{0.2in} & {\\tt et} & ::= & {\\tt Ar(i)}\;|\;{\\tt Paar(a,i)}\n"^
              "\end{array}$$\n"^
              "The rewriting system of the suspension calculus is given by:\n"^
              "\\begin{center}\n"^
              "\\begin{tabbing}\n"^
	      
              "\(\ \) (r11)\quad\=\kill\n"^
              "\(\ \) (\(\\beta_s\))\> \(((\lambda.t_1)\; t_2) \\rightarrow \env{t_1, 1,0, (t_2,0) :: nil}\)\\\[2mm]\n"^
              "\(\ \) (\(\\beta_s'\))\> \(((\lambda.\env{t_1,ol+1,nl+1,\dum{nl} :: e})\; t_2) \\rightarrow \env{t_1, ol+1,nl, (t_2,nl) :: e}\)\\\[2mm]\n"^
              "\(\ \) (r1)\> \(\env{c,ol,nl,e} \\rightarrow c\), where \(c\) is a constant\@.\\\[2mm]\n"^
              "\(\ \) (r2)\> \(\env{x,ol,nl,e} \\rightarrow c\), where \(x\) is an instantiatable variable\@.\\\[2mm]\n"^
              "\(\ \) (r3)\>\(\env{\db{i},ol,nl,e} \\rightarrow\db{i - ol + nl}\), if \(i>ol\)\@.\\\[2mm]\n"^
              "\(\ \) (r4)\>\(\env{\db{i},ol,nl,e} \\rightarrow\db{nl - l}\), if \(i\leq ol\) and \(e[i]=\dum{l}\)\@.\\\[2mm]\n"^
              "\(\ \) (r5)\>\(\env{\db{i},ol,nl,e} \\rightarrow\env{t,0,nl-l,nil}\), if \(i\leq ol\) and \(e[i]=(t,l)\)\@.\\\[2mm]\n"^
              "\(\ \) (r6)\> \(\env{(t_1\; t_2),ol,nl,e} \\rightarrow(\env{t_1,ol,nl,e}\;\env{t_2,ol,nl,e})\)\@.\\\[2mm]\n"^
              "\(\ \) (r7)\>\(\env{(\lambda.t), ol, nl, e} \\rightarrow(\lambda.\env{t,ol + 1, nl + 1, \dum{nl} :: e})\)\@.\\\[2mm]\n"^
              "\(\ \) (r8)\>\(\env{\env{t,ol,nl,e},0, nl', nil} \\rightarrow \env{t,ol,nl+nl',e}\)\@.\\\[2mm]\n"^
              "\(\ \) (r9)\> \(\env{t,0,0,nil} \\rightarrow t\)\@.\\\[2mm]\n"^
              "\(\ \) (r10)\>\(\env{\db{i},ol,nl,e} \\rightarrow t\), if \(i\leq ol\) and \(e[i]=(t,l)\) and \(nl= l\)\@.\\\[2mm]\n"^
              "\(\ \) (r11)\>\(\env{\db{i},ol,nl,e} \\rightarrow  \env{t,ol',nl'+nl-l,e'}\), if \(i\leq ol\) and \(e[i]=(\env{t,ol',nl',e'},l)\) and \(nl\\not= l\)\@.\\\[2mm]\n"^
              "\(\ \) (Eta)\> \(\lambda.(t_1 \;\db{1}) \\rightarrow t_2 \), \hspace{.1in} if \hspace{.05in}  \(t_1 =_{r} \env{t_2, 0, 1, nil}\)\@.\n"^
              "\end{tabbing}\n"^
              "\end{center}\n"^
              "The Eta rule defined for this calculus is the one of the Suspension calculus.\n"^
              "\end{document}\n"
          )
      | _ -> assert false
  in          
    Unix.close output_file_desc;
    Unix.system ("latex " ^ output_file_name);  
    Unix.system ("xdvi " ^ output_file_name ^" & ")
      
