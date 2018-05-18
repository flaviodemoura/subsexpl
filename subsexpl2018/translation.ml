(*   1. <expr> ::= <identifier>                    *)
(*   2. <expr> ::= (λ <identifier>. <expr>)            *)
(*   3. <expr> ::= (<expr> <expr>)                *)

open Char
open List
open Buffer
open Printf
open String

open Setypes

exception Empty_list

(** Sentence in the usual lambda calculus, here we allow strings as
    identifiers for ease reading. *)
type identifier = string
type lambda_sentence =
  | Identifier of identifier
  | Lambda of identifier * lambda_sentence
  | Application of lambda_sentence * lambda_sentence

(** Sentence in deBruijn notation. *)
type deBruijn_lambda_sentence =
  | DeBruijn_Identifier of int
  | DeBruijn_Lambda of deBruijn_lambda_sentence
  | DeBruijn_Application of deBruijn_lambda_sentence * deBruijn_lambda_sentence

(** Intermediate notation where binded variables are in deBruijn
    notation and free variables use names. *)
type deBruijn_lambda_sentence_intermediate_result =
  | DeBruijn_FreeVariable of identifier
  | DeBruijn_BindedVariable of int
  | DeBruijn_Lambda_IE of deBruijn_lambda_sentence_intermediate_result
  | DeBruijn_Application_IE of deBruijn_lambda_sentence_intermediate_result * deBruijn_lambda_sentence_intermediate_result

(** The parTraducaoDeBruijn type relates an identifier with the
    corresponding integer in deBruijn notation. *)
type parTraducaoDeBruijn = identifier * int

(** The following types represent lists for free and bound variables,
    respectively. *)
type freeVariableList = parTraducaoDeBruijn list
type bindedVariableList = parTraducaoDeBruijn list
(*
type variablelist = freeVariableList * bindedVariableList 
*)

(* Lexer for the simple lambda calculus *)
(*--------------------------------------*)

(** This is the parser. *)

let rec construct_lambdas (identifierList : identifier list) (lambdaExpression : lambda_sentence) : lambda_sentence =
  match identifierList with
    | [head]        -> Lambda(head, lambdaExpression)
    | head :: tail  -> Lambda(head, (construct_lambdas tail lambdaExpression))
    | _             -> assert false

let rec construct_applications_helper (lambdaExpressionList : lambda_sentence list) (currentExpression : lambda_sentence) : lambda_sentence =
  match lambdaExpressionList with
    | []           -> currentExpression
    | head :: tail -> construct_applications_helper tail (Application(currentExpression,head))

let rec construct_applications (lambdaExpressionList : lambda_sentence list) : lambda_sentence = 
  match lambdaExpressionList with
    | []           -> assert false
    | [head]       -> head
    | head :: tail -> construct_applications_helper tail head

let rec getVariableTranslation (lista : parTraducaoDeBruijn list) (identifier : string) : int =
  match lista with
      [] -> -1
    | (currentIdentifier, index) :: tail    
        when currentIdentifier = identifier    -> index
    | head :: tail -> getVariableTranslation tail identifier

let rec getVariableTranslationByIndex (lista : parTraducaoDeBruijn list) (identifier : int) : string =
  match lista with
      [] -> "Variable not found"
    | (currentIdentifier, index) :: tail    
        when index = identifier    -> currentIdentifier
    | head :: tail                                                                            
      -> getVariableTranslationByIndex tail identifier

let containsVariableTranslation (lista : parTraducaoDeBruijn list) (identifier : string) : bool =
  if (getVariableTranslation lista identifier) == -1 
  then false
  else true
    
let different (element1 : string) (element2 : string) : bool =
  if compare element1 element2 != 0
  then true
  else false

let rec removeDuplicateElements (lista : 'a list) : ('a list) =
  match lista  with
      []                -> []
    | head :: tail      -> head :: removeDuplicateElements (filter (different head) tail)

let rec createFreeVariableTranslationHelper 
    (deBruijnLambda : deBruijn_lambda_sentence_intermediate_result) 
    (currentTranslation : freeVariableList) : freeVariableList =
  match deBruijnLambda with 
    | DeBruijn_FreeVariable freeVariable 
        when (containsVariableTranslation currentTranslation freeVariable) -> currentTranslation 
    | DeBruijn_FreeVariable freeVariable 
        (* otherwise *) ->  append currentTranslation [(freeVariable,(List.length currentTranslation)+1)]
    | DeBruijn_BindedVariable bindedVariable        -> currentTranslation
    | DeBruijn_Lambda_IE(deBruijn_lambda_sentence) -> 
        createFreeVariableTranslationHelper deBruijn_lambda_sentence currentTranslation
    | DeBruijn_Application_IE(sentence_applying, sentence_being_applied) -> 
        let translationLeft = createFreeVariableTranslationHelper sentence_applying currentTranslation in
          createFreeVariableTranslationHelper sentence_being_applied translationLeft

let createFreeVariableTranslation 
    (deBruijnLambda : deBruijn_lambda_sentence_intermediate_result) : freeVariableList =
  createFreeVariableTranslationHelper deBruijnLambda []

let rec convertDeBruijnIntermediateResult2DeBruijnHelper 
    (deBruijnIntermediateLambda : deBruijn_lambda_sentence_intermediate_result) 
    (freeVariableTranslationList : freeVariableList) (lambdaIndex : int) : deBruijn_lambda_sentence =
  match deBruijnIntermediateLambda with 
    | DeBruijn_FreeVariable freeVariable            -> 
        DeBruijn_Identifier((getVariableTranslation freeVariableTranslationList freeVariable) + lambdaIndex)
    | DeBruijn_BindedVariable bindedVariable        -> 
        DeBruijn_Identifier(bindedVariable)
    | DeBruijn_Lambda_IE(deBruijn_lambda_sentence) -> 
        DeBruijn_Lambda(convertDeBruijnIntermediateResult2DeBruijnHelper deBruijn_lambda_sentence freeVariableTranslationList (lambdaIndex+1))
    | DeBruijn_Application_IE(sentence_applying, sentence_being_applied) -> 
        DeBruijn_Application(
          (convertDeBruijnIntermediateResult2DeBruijnHelper sentence_applying freeVariableTranslationList lambdaIndex),
          (convertDeBruijnIntermediateResult2DeBruijnHelper sentence_being_applied freeVariableTranslationList lambdaIndex))

let convertDeBruijnIntermediateResult2DeBruijn  
    (deBruijnIntermediateLambda : deBruijn_lambda_sentence_intermediate_result) : deBruijn_lambda_sentence =
  convertDeBruijnIntermediateResult2DeBruijnHelper deBruijnIntermediateLambda (createFreeVariableTranslation deBruijnIntermediateLambda) 0

(** Dada uma lista de tradução, se já existir o identificador nesta,
    associa um novo índice a este, senão o mesmo será adicionado no
    final desta nova tradução **)
let rec assignId (translationList : parTraducaoDeBruijn list) 
    (stringId : string) (newIndex : int) : parTraducaoDeBruijn list =
  match translationList with
    | [] -> [(stringId, newIndex)]
    | (identifier, currentIndex) :: tail  when stringId = identifier -> (stringId, newIndex) :: tail
    | head :: tail -> head :: (assignId tail stringId newIndex)

let incrementIdentifier (par : parTraducaoDeBruijn) : parTraducaoDeBruijn =
  match par with (identifier, index) -> (identifier, index+1)
    
(** Aumenta em 1 o índice de todas traduções presentes **)
let incrementTranslationList (translationList : parTraducaoDeBruijn list) : parTraducaoDeBruijn list =
  map incrementIdentifier translationList

(** Adiciona um novo identificador para tradução, incrementando todos antigos **)
let rec assignNewId (translationList : parTraducaoDeBruijn list) (stringId : string) : parTraducaoDeBruijn list =
  (stringId, 1) :: incrementTranslationList translationList

let rec convertSimpleLambda2DeBruijnIntermediateResult 
    (simpleLambda: lambda_sentence) 
    (bindedList : bindedVariableList) : 
    deBruijn_lambda_sentence_intermediate_result = 
  match simpleLambda with 
    | Identifier identifier when (containsVariableTranslation bindedList identifier) -> 
	DeBruijn_BindedVariable(getVariableTranslation bindedList identifier) 
    | Identifier identifier ->  DeBruijn_FreeVariable(identifier)
    | Lambda(identifier, sentence) ->
	DeBruijn_Lambda_IE(convertSimpleLambda2DeBruijnIntermediateResult sentence (assignNewId bindedList identifier))
    | Application(sentence_applying, sentence_being_applied) -> 
	DeBruijn_Application_IE( (convertSimpleLambda2DeBruijnIntermediateResult sentence_applying bindedList), 
				 (convertSimpleLambda2DeBruijnIntermediateResult sentence_being_applied bindedList))

let rec convertSimpleLambda2DeBruijnIntermediate 
    (simpleLambda: lambda_sentence) : deBruijn_lambda_sentence_intermediate_result = 
  convertSimpleLambda2DeBruijnIntermediateResult simpleLambda [] 

let rec convertDeBruijn2DeBruijnIntermediateResultHelper 
    (deBruijnLambda : deBruijn_lambda_sentence)
    (freeVariableTranslationList : freeVariableList) (lambdaIndex : int) : 
    deBruijn_lambda_sentence_intermediate_result = 
  match deBruijnLambda with 
      DeBruijn_Identifier identifier when (identifier > lambdaIndex) -> 
	DeBruijn_FreeVariable(getVariableTranslationByIndex freeVariableTranslationList (identifier-lambdaIndex)) 
    | DeBruijn_Identifier identifier (* otherwise *) -> DeBruijn_BindedVariable(identifier)
    | DeBruijn_Lambda(deBruijn_lambda_sentence) -> 
	DeBruijn_Lambda_IE(convertDeBruijn2DeBruijnIntermediateResultHelper deBruijn_lambda_sentence freeVariableTranslationList (lambdaIndex+1))
    | DeBruijn_Application(sentence_applying, sentence_being_applied)  -> 
	DeBruijn_Application_IE(
          convertDeBruijn2DeBruijnIntermediateResultHelper sentence_applying freeVariableTranslationList lambdaIndex,
          convertDeBruijn2DeBruijnIntermediateResultHelper sentence_being_applied freeVariableTranslationList lambdaIndex)        

let convertDeBruijn2DeBruijnIntermediateResult (deBruijnLambda : deBruijn_lambda_sentence) (freeVariableTranslationList : freeVariableList) : 
    deBruijn_lambda_sentence_intermediate_result =       
  convertDeBruijn2DeBruijnIntermediateResultHelper deBruijnLambda freeVariableTranslationList 0

let rec print_simple_lambda simpleLambda = 
  match simpleLambda with 
      Identifier identifier -> print_string identifier
    | Lambda(identifier, sentence) -> 
        print_string "L("; 
        print_string identifier; 
        print_string ","; 
        print_simple_lambda sentence; 
        print_string ")";
    | Application(sentence_applying, sentence_being_applied) ->         
        print_string "(";
        print_simple_lambda sentence_applying;
        print_string " ";
        print_simple_lambda sentence_being_applied;
        print_string ")"

let rec print_deBruijn_lambda_intermediate deBruijnLambda = 
  match deBruijnLambda with 
      DeBruijn_FreeVariable freeVariable -> print_string freeVariable
    | DeBruijn_BindedVariable bindedVariable -> print_int bindedVariable
    | DeBruijn_Lambda_IE(deBruijn_lambda_sentence) -> 
        print_string "L("; 
        print_deBruijn_lambda_intermediate deBruijn_lambda_sentence; 
        print_string ")";
    | DeBruijn_Application_IE(sentence_applying, sentence_being_applied) ->         
        print_string "(";
        print_deBruijn_lambda_intermediate sentence_applying;
        print_string " ";
        print_deBruijn_lambda_intermediate sentence_being_applied;
        print_string ")"

let rec print_deBruijn_lambda_intermediate_parecendo_entradaHelper deBruijnLambda lambdaDepth = 
  match deBruijnLambda with 
      DeBruijn_FreeVariable freeVariable -> print_string freeVariable
    | DeBruijn_BindedVariable bindedVariable -> print_int bindedVariable
    | DeBruijn_Lambda_IE(deBruijn_lambda_sentence) -> 
        print_string "(\\";
        print_int lambdaDepth;
        print_string "."; 
        print_deBruijn_lambda_intermediate_parecendo_entradaHelper deBruijn_lambda_sentence (lambdaDepth+1); 
        print_string ")";
    | DeBruijn_Application_IE(sentence_applying, sentence_being_applied) ->         
        print_string "(";
        print_deBruijn_lambda_intermediate_parecendo_entradaHelper sentence_applying lambdaDepth;
        print_string " ";
        print_deBruijn_lambda_intermediate_parecendo_entradaHelper sentence_being_applied lambdaDepth;
        print_string ")"

let print_deBruijn_lambda_intermediate_parecendo_entrada deBruijnLambda = 
  print_deBruijn_lambda_intermediate_parecendo_entradaHelper deBruijnLambda 1

let rec return_representation_deBruijn_Lambda deBruijnLambda =
  match deBruijnLambda with 
      DeBruijn_Identifier identifier -> string_of_int identifier
    | DeBruijn_Lambda(deBruijn_lambda_sentence) ->
        "L(" ^ return_representation_deBruijn_Lambda deBruijn_lambda_sentence ^ ")"
    | DeBruijn_Application(sentence_applying, sentence_being_applied) -> 
        "A(" ^ (return_representation_deBruijn_Lambda sentence_applying) ^
          "," ^ (return_representation_deBruijn_Lambda sentence_being_applied) ^
          ")"

let rec print_deBruijn_lambda deBruijnLambda = 
  match deBruijnLambda with 
      DeBruijn_Identifier identifier -> print_int identifier
    | DeBruijn_Lambda(deBruijn_lambda_sentence) -> 
        print_string "L("; 
        print_deBruijn_lambda deBruijn_lambda_sentence; 
        print_string ")";
    | DeBruijn_Application(sentence_applying, sentence_being_applied) ->         
        print_string "A(";
        print_deBruijn_lambda sentence_applying;
        print_string ",";
        print_deBruijn_lambda sentence_being_applied;
        print_string ")"
	  
let rec print_translationList lista =
  match lista with
    | []	->	print_string ""
    | (identifier, integer) :: rest	-> 
	print_string identifier;
	print_string " -> ";
	print_int integer;
        print_string ", ";
	print_translationList rest

let rec getBindedVariablesNames (simpleLambda : exlambda) : string list =
  match simpleLambda with  
    | DB identifier -> []  
    | L(sentence,identifier,_)
      -> identifier :: (getBindedVariablesNames sentence)
    | A(sentence_applying, sentence_being_applied)
      -> append (getBindedVariablesNames sentence_applying) 
        (getBindedVariablesNames sentence_being_applied) 
    | _ -> assert false

let rec getVariableListFromTranslation (variableList : parTraducaoDeBruijn list) : string list =
  match variableList with
    | []                          -> []
    | (id,num) :: tail -> id :: (getVariableListFromTranslation tail)

let rec print_list_string (stringList : string list) =
  match stringList with
    | []         -> []
    | id :: tail -> print_string (id ^ ",") ; print_list_string tail

let rec convertSimpleLambda2deBruijn_helper 
    (simpleLambda: lambda_sentence) 
    (bindedList : bindedVariableList) 
    (freeList : freeVariableList)
    (lambdaDepth : int) : exlambda = 
  match simpleLambda with 
    | Identifier identifier when (containsVariableTranslation bindedList identifier)
        ->  DB(getVariableTranslation bindedList identifier) 
    | Identifier identifier
      ->  DB(lambdaDepth + (getVariableTranslation freeList identifier))
    | Lambda(identifier, sentence) ->
        L(convertSimpleLambda2deBruijn_helper sentence (assignNewId bindedList identifier) freeList (lambdaDepth+1), identifier, BaseType("A"))
    | Application(sentence_applying, sentence_being_applied) ->
        let result_sentence_applying = (convertSimpleLambda2deBruijn_helper sentence_applying bindedList freeList lambdaDepth) in
        let result_sentence_applied = (convertSimpleLambda2deBruijn_helper sentence_being_applied bindedList freeList lambdaDepth) in
          A(result_sentence_applying,                    
            result_sentence_applied)

let convertSimpleLambda2deBruijn (simpleLambda: lambda_sentence) : exlambda = 
  let freeVariableTranslation = 
    (createFreeVariableTranslation (convertSimpleLambda2DeBruijnIntermediate simpleLambda)) in
    convertSimpleLambda2deBruijn_helper simpleLambda [] freeVariableTranslation 0


(** This is the main loop that calls each calculus separately. *)
(*
  let rec main_loop() =
  let simple_lambda = input_line stdin in
  let simpleLambdaResult = convertStr2SimpleLambda simple_lambda in
  let intermediateResult = convertSimpleLambda2DeBruijinIntermediate simpleLambdaResult in
  let deBruijinResult = convertDeBruijinIntermediateResult2DeBruijin intermediateResult in
  let freeVariableTranslation = createFreeVariableTranslation intermediateResult in
  let intermediateReconverted = convertDeBruijin2DeBruijinIntermediateResult deBruijinResult freeVariableTranslation in

  print_string "Simple Lambda: ";
  print_simple_lambda simpleLambdaResult;
  print_newline ();
  print_string "DeBruijinIntermediate: ";
  print_deBruijin_lambda_intermediate intermediateResult;
  print_newline ();
  subexpl_     print_string "DeBruijinIndices: ";
  print_deBruijin_lambda deBruijinResult;
  print_newline ();
  print_string "Free Variable Translation list: ";
  print_translationList freeVariableTranslation;
  print_newline ();
  print_string "DeBruijinIntermediate Thru Translation of Free Variables: ";
  print_deBruijin_lambda_intermediate intermediateReconverted;
  print_newline ();        
  print_string "Traduzindo para a entrada inicial: ";
  print_deBruijin_lambda_intermediate_parecendo_entrada intermediateReconverted;
  print_newline ();        
  print_newline ();
  main_loop()


  let _ =
(*
  if Array.length Sys.argv = 2
  then
  let f = open_in Sys.argv.(1) in
  Input.input_file := Some f;
  main_loop ()
  else
*)
    main_loop ()

*)
