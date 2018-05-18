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

(** This module contains the main loop for the pure lambda calculus with the usual notation with identifiers.
  @author Flavio L. C. de Moura
  @author M. Ayala-Rincon 
  @author F. Kamareddine 
  @author Flavio B. Botelho *)   

open Setypes
open Translation
open Maybe

(* Return the last element of the list *)
let last lst = let lastind = List.length lst in List.nth lst (lastind-1);;


let rec print_lambda_variables (lambdaVariables : string list) (numberToPrint : int) =
    match numberToPrint with
    | 0 -> print_string ".";
    | 1 -> print_string (List.nth lambdaVariables (numberToPrint-1)); 
           print_lambda_variables lambdaVariables (numberToPrint-1)
    | _ -> print_string (List.nth lambdaVariables (numberToPrint-1)); 
           print_string ",";
           print_lambda_variables lambdaVariables (numberToPrint-1)


let rec insertNewVariableWithNumber (newVariable : string) (lambdaVariables : string list) (number : int) : string list =
    let newVariableWithNumber = newVariable ^ "_" ^ (string_of_int number) in
    if List.exists (fun x -> (compare x  newVariableWithNumber) == 0) lambdaVariables 
    then insertNewVariableWithNumber newVariable lambdaVariables (number+1)
    else newVariableWithNumber :: lambdaVariables

let insertNewVariable (newVariable : string) (lambdaVariables : string list) : string list =
    if List.exists (fun x -> (compare x newVariable) == 0) lambdaVariables 
    then insertNewVariableWithNumber newVariable lambdaVariables 1
    else newVariable :: lambdaVariables

let rec count_lambdas exp : int =
    match exp with
    | L(e,_,_) -> 1 + (count_lambdas e)
    | _ -> 0

let rec get_lambda_variables exp (lambdaVariables : string list) : string list =
    match exp with
    | L(e,variable_name,_) -> 
        let newVariableList = (insertNewVariable variable_name lambdaVariables) in 
            get_lambda_variables e newVariableList
    | _ -> lambdaVariables

let rec get_exp_after_lambdas exp : exlambda =
    match exp with
    | L(e,variable_name,_) -> get_exp_after_lambdas e 
    | _ -> exp

let rec print_exp_lse_only_simple_lambda_helper (lambdaVariables : string list) (traducao : parTraducaoDeBruijn list) exp = 
  let lambda_depth = List.length lambdaVariables in
  let variableList = get_lambda_variables exp lambdaVariables in
  let nextExpression = get_exp_after_lambdas exp in
  let numberOfLambdas = count_lambdas exp in
  match exp with 
    | DB i -> 
        if i > lambda_depth
            then print_string (getVariableTranslationByIndex traducao (i-lambda_depth))
            else print_string (List.nth lambdaVariables (i-1))
    | A(e1,e2) ->
        (** FIXME: Achar meio de eliminar parenteses desnecessários *)
        print_string "(";
        print_exp_lse_only_simple_lambda_helper lambdaVariables traducao e1;
        print_string "  ";
        print_exp_lse_only_simple_lambda_helper lambdaVariables traducao e2;
        print_string ")"
    | L(e,variable_name,_) -> 
        (** FIXME: Achar meio de eliminar parenteses desnecessários *)
        print_string "(\\";
        print_lambda_variables variableList numberOfLambdas;
        print_exp_lse_only_simple_lambda_helper variableList traducao nextExpression;
        print_string ")"
    | TermAlias(s) -> print_string s
    | _ -> assert false

let print_exp_lse_only_simple_lambda (traducao : parTraducaoDeBruijn list) exp = 
    print_exp_lse_only_simple_lambda_helper (List.map fst traducao) traducao exp

let convertStr2SimpleLambda s = 
    let lexbuf = Lexing.from_string (s ^ "\n") in
        Subexpl_parser.main Subexpl_lexer.token lexbuf 


(** Alias for terms *)
type alias = string * exlambda

let rec trim s =
    let l = String.length s in
        if l=0 then s
            else 
                if s.[0]=' ' || s.[0]='\t' || s.[0]='\n' || s.[0]='\r' then
                    trim (String.sub s 1 (l-1))
                else if s.[l-1]=' ' || s.[l-1]='\t' || s.[l-1]='\n' || s.[l-1]='\r' then
                    trim (String.sub s 0 (l-1))
            else
                s


let createAlias (input : string) : alias =
    let splitedString = Str.split (Str.regexp "=") input in
    let aliasName = trim (List.nth splitedString 0) in
    let stringLambdaTerm = trim (List.nth splitedString 1) in
    let simpleLambdaTerm = convertStr2SimpleLambda stringLambdaTerm in
    let lambdaTerm = Translation.convertSimpleLambda2deBruijn simpleLambdaTerm  in
        (aliasName, lambdaTerm)

(* Assumindo que não existem variáveis livres no Alias,
    melhor criar check em algum lugar para isso *)
let printAlias (alias : alias) =
    match alias with
        (name, term) ->
            print_string (name ^ "=>");
            print_exp_lse_only_simple_lambda [] term;
            print_string  "\n"

let printAliasList (aliasList : alias list) =
    List.iter printAlias aliasList

(* From http://pleac.sourceforge.net/pleac_ocaml/strings.html *)
let slurp_to_list filename =
  let ic = open_in filename and
  l = ref [] in
  let rec loop () =
    let line = input_line ic in
    l := line::!l;
    loop () in
  try loop () with End_of_file -> close_in ic; List.rev !l;;

let readAliasFile (filename : string) : alias list =
    List.map createAlias (slurp_to_list filename) 

let rec createLambdaNumber_helper n =
    match n with
        | 0 -> DB 1
        | _ -> A(DB 2, createLambdaNumber_helper (n-1))

let createLambdaNumber n =
    L(L(createLambdaNumber_helper n, "x", BaseType "S"), "f", BaseType "S->S")

let rec convertAlias 
    lambda_depth 
    aliasList 
    (traducao : parTraducaoDeBruijn list) 
    exp = 
  match exp with 
    | DB i -> 
        if i > lambda_depth
            then 
            (
            try
        Pervasives.snd (List.find (fun x -> (String.compare (Pervasives.fst x) (getVariableTranslationByIndex traducao (i-lambda_depth))) == 0) aliasList)
            with Not_found -> 
                (
                try createLambdaNumber (int_of_string (getVariableTranslationByIndex traducao (i-lambda_depth)))
                with Failure _ -> exp
                )
            )
            else exp
    | A(e1,e2) ->
        A(
            convertAlias lambda_depth aliasList traducao e1,
            convertAlias lambda_depth aliasList traducao e2
        )
    | L(e,variable_name,ltype) -> 
        L(
            convertAlias (lambda_depth+1) aliasList traducao e,
            variable_name,
            ltype
        )
    | _ -> assert false

;;



let rec matchTerms (term1:Setypes.exlambda) (term2: Setypes.exlambda) : bool =
    match term1 with
    | DB(i) -> 
        term2 == term1 
    | A(e11,e12) -> (
        match term2 with
            | A(e21,e22) -> (matchTerms e11 e21) && (matchTerms e12 e22)
            | _          -> false )
    | L(e1,_,_) -> (
        match term2 with
            | L(e2,_,_) -> (matchTerms e1 e2)
            | _         -> false )
    | _ -> false


let isNumber (term:Setypes.exlambda) : bool =
    let rec isNumber_helper exp =
        match exp with
            | A(e1,e2) -> 
                 (e1 = (DB 2)) && (isNumber_helper e2)
            | DB(1)    -> true
            | _        -> false
    in
    match term with
        | L(L(e,_,_),_,_) -> isNumber_helper e
        | _ -> false


let getNumber (term:Setypes.exlambda) : int =
    let rec getNumber_helper exp =
        match exp with
            | A(e1,e2) -> 1 + (getNumber_helper e2)
            | DB(1)    -> 0
            | _        -> assert false
    in
    match term with
        | L(L(e,_,_),_,_) -> getNumber_helper e
        | _ -> assert false

let rec matchTermWithAlias (term:Setypes.exlambda) (aliasList : alias list) : string maybe =
    try
        Just (Pervasives.fst (List.find (fun x -> matchTerms (Pervasives.snd x) term) aliasList))
    with Not_found -> Nothing

let matchWithKnownTerms (term:Setypes.exlambda) (aliasList : alias list) : string maybe = 
    let aliasResult = matchTermWithAlias term aliasList in
        match aliasResult with
            | Just a -> aliasResult
            | Nothing ->
                if isNumber term then Just (string_of_int (getNumber term))
                else Nothing

let value x =
    match x with
        | Just a -> a
        | _      -> assert false

let rec modifyTermByAlias (exp:Setypes.exlambda) (aliasList : alias list) =   
    let termMatch = matchWithKnownTerms exp aliasList in
    if (termMatch == Nothing) then
    (
        match exp with 
            | DB i -> exp
            | A(e1,e2) ->
                A(modifyTermByAlias e1 aliasList, modifyTermByAlias e2 aliasList)
            | L(e,v,t) -> 
                L(modifyTermByAlias e aliasList, v, t)
            | _ -> assert false
    )
    else
        TermAlias(value termMatch)

(** This is the main loop used for the simulation of the pure lambda calculus. *)
let rec lnomesse f =
  try
    let init_exp = Input.ask_exp convertStr2SimpleLambda in
    let simple_lambda_sentence = convertStr2SimpleLambda init_exp in
    let freeVariableTranslation = Translation.createFreeVariableTranslation (convertSimpleLambda2DeBruijnIntermediate simple_lambda_sentence) in
    let aliasList = (readAliasFile "alias_common.txt")@(readAliasFile "alias.txt") in 
    let i_upl = [(convertAlias 0 aliasList freeVariableTranslation (Translation.convertSimpleLambda2deBruijn simple_lambda_sentence), 0, [], "")] in
    let print_expression = (fun x -> print_exp_lse_only_simple_lambda freeVariableTranslation (modifyTermByAlias x aliasList)) in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = Sepure.lst_pure c_exp in
        print_newline();
        print_string "Expression: ";
        print_expression c_exp;
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
            print_newline();
            Output.print_history (List.rev l_upl) (print_expression); 
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


(** This is the main loop used for the simulation of the pure lambda
    calculus with names. *)
let lnomessusp f =
  try
    let init_exp = Input.ask_exp convertStr2SimpleLambda in
    let simple_lambda_sentence = convertStr2SimpleLambda init_exp in
    let freeVariableTranslation = Translation.createFreeVariableTranslation (convertSimpleLambda2DeBruijnIntermediate simple_lambda_sentence) in
    let i_upl = [(Translation.convertSimpleLambda2deBruijn simple_lambda_sentence,0,[],"")] in
    let rec internal_loop l_upl = 
      let c_exp = Common.first(List.hd l_upl) in
      let lst_ex = Sepure.lst_purecomb c_exp in
        print_newline();
        print_string "Expression: ";
        print_exp_lse_only_simple_lambda freeVariableTranslation c_exp;
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
		    print_newline();
		    Output.print_history (List.rev l_upl) (print_exp_lse_only_simple_lambda freeVariableTranslation); 
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
