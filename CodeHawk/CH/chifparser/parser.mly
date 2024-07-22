%{
(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: A. Cody Schuffelen
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2023 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

open Lexing
open CHCommon
open CHPretty
open CHNumerical
open CHLanguage
open CHOnlineCodeSet
open CHStaticChecker
open ParseError
open CHCollections

let doError(s) =
  let sp = Parsing.rhs_start_pos 1 in
  raise (Parse_failure ((sp.pos_lnum),(sp.pos_cnum-sp.pos_bol),(s)))


let symbol ?(atts = []) s = new symbol_t ~atts:atts s;;


module F = LanguageFactory


let curScope = ref (F.mkScope())


module SymbolTable =
  Hashtbl.Make(struct
		type t = symbol_t
		let equal n1 n2 = ((n1#getBaseName)=(n2#getBaseName))
		let hash n = Hashtbl.hash (n#getBaseName)
	      end)


module VariableTable =
  Hashtbl.Make(struct
		type t = variable_t
		let equal n1 n2 = ((n1#getName#getBaseName)=(n2#getName#getBaseName))
		let hash n = Hashtbl.hash (n#getName#getBaseName)
	      end)

let varTable : ( variable_t ) SymbolTable.t = SymbolTable.create 1


let sigTable : ( variable_type_t ) SymbolTable.t = SymbolTable.create 1


let rec addCFGEdges (cfg : CHLanguage.cfg_int)(from)(toList) =
  match toList with
  | [] -> ()
  | first :: rest -> (cfg#addEdge(from)(first) ; addCFGEdges(cfg)(from)(rest);)


let addCFGState cfg stateData =
  let name, state, outgoingList = stateData in
  begin
    addCFGEdges(cfg)(name)(outgoingList)
  end


let rec addCFGStates(cfg)(stateDataList) =
  match stateDataList with
  | [] -> ()
  | (name, state, outgoingList) :: rest ->
     (cfg#addState state ; addCFGStates(cfg)(rest) ; addCFGState cfg (name,state, outgoingList))


let temporaryTypeTable : (variable_type_t) SymbolTable.t = (SymbolTable.create 1)
let temporaryTable : (variable_t) SymbolTable.t = (SymbolTable.create 1)


let scopeHandleVar (sym : symbol_t) ( typ : variable_type_t ) =
  if not( SymbolTable.mem varTable sym ) then
    (if not (is_temporary_type typ) then
       let ret = (!curScope)#mkVariable(sym)(typ) in
       (
	 SymbolTable.add varTable sym ret ;
       )
     else
       SymbolTable.add temporaryTypeTable sym typ)


let parse_error s = print_endline s


let inTransaction = ref false
let startedTransaction = ref false


let arithTmpCounter = ref 1
let arithPrefix = ref "A"


let handleTransaction() =
  if(not !inTransaction) then
    if(not !startedTransaction) then begin
	startedTransaction := true ;
	!curScope#startTransaction ;
	SymbolTable.clear temporaryTable
      end

let beginTransaction() =
  begin
    inTransaction := true ;
    !curScope#startTransaction ;
  end


let endTransaction() =
  begin
    inTransaction := false ;
    !curScope#endTransaction ;
    SymbolTable.clear temporaryTable
  end


let getVar sym =
  if SymbolTable.mem temporaryTypeTable sym then
    (if SymbolTable.mem temporaryTable sym then
       SymbolTable.find temporaryTable sym
     else
       let newVar =
	 match SymbolTable.find temporaryTypeTable sym with
	 | NUM_TMP_VAR_TYPE -> (!curScope)#requestNumTmpVariable
	 | NUM_TMP_ARRAY_TYPE -> (!curScope)#requestNumTmpArray
	 | SYM_TMP_VAR_TYPE -> (!curScope)#requestSymTmpVariable
	 | SYM_TMP_ARRAY_TYPE -> (!curScope)#requestSymTmpArray
	 | _ -> doError "temporary type not temporary"
       in
       begin
	 (SymbolTable.add temporaryTable sym newVar) ;
	 newVar
       end)
  else SymbolTable.find varTable sym
%}

%token T_Procedure
%token T_Transaction
%token T_Bindings
%token T_Scope
%token T_Loop
%token T_When
%token T_Assert
%token T_Numerical T_Symbolic T_NumericalArr T_SymbolicArr
%token T_TempNumerical T_TempSymbolic T_TempNumericalArr T_TempSymbolicArr
%token T_Num_Loop_Counter
%token T_Operation
%token T_Cfg T_Entry T_Exit
%token T_Goto T_Goto_Block
%token T_Break T_Breakout_Block
%token T_Skip
%token T_Label
%token T_Table
%token T_Domains
%token T_Domain_Cmd
%token T_Read T_Write T_Read_Write
%token T_Struct
%token T_Code
%token T_Relation
%token T_Abstract_Vars
%token T_Abstract_Elts
%token T_Branch
%token T_Context
%token T_Call
%token T_Move_Values
%token T_Of
%token T_On
%token T_Move_Relations
%token T_Over
%token T_Select
%token T_Insert T_Into T_Values
%token T_Delete
%token T_Assign_Table
%token T_Do
%token T_Random T_True T_False
%token T_In T_Not
%token T_Rows T_Where T_From
%token T_And
%token T_As

%token T_LParen T_RParen T_LSquareBracket T_RSquareBracket T_LCurlyBracket T_RCurlyBracket
%token T_Colon
%token T_Equals T_EqualsArrow
%token T_Arrow
%token T_Plus T_Minus T_Star T_Slash
%token T_DoubleVLine T_DoubleColon
%token T_Shift
%token T_LessThan T_LessThanEqualTo T_GreaterThan T_GreaterThanEqualTo
%token T_EqualTo T_NotEqualTo
%token T_Comma T_Semicolon
%token T_Hash

%token <string> T_Symbol
%token <string> T_Identifier
%token <Big_int_Z.big_int> T_Num

%token T_Eof

%type <CHLanguage.procedure_int list> program
%type <('a, 'b) CHLanguage.command_t list> Equality Command CommandList

%left Plus T_Plus Minus T_Minus
%left RootPlus RootMinus
%left Div T_Slash Mult T_Star
%left RootDiv RootMult


%start program

%%

program	                : ProcedureList T_Eof	{ $1 }
			;

ProcedureList	        :			  { [] }
			| Procedure ProcedureList { $1 :: $2 }
			;

Procedure		: MakeProcedureScope T_Procedure Var Signature Bindings Scope ProcedureBody	{ F.mkProcedure $3 $4 $5 $6 $7 }
			| error									        { doError "error in procedure" }
			;

MakeProcedureScope	: { begin curScope := F.mkScope() ; SymbolTable.clear varTable end }
			;

Signature		: T_LParen SignatureArgList T_RParen	{ $2 }
			| error					{ doError "error in signature" }
			;

SignatureArgList	:			{ [] }
			| RealSignatureArgList	{ $1 }
			;

RealSignatureArgList	: SignatureArg					{ [$1] }
			| SignatureArg T_Comma RealSignatureArgList	{ $1 :: $3 }
			| error						{ doError "error in signature argument list" }
			;

SignatureArg	        : ArgMode Var T_Colon VarType	{ let ret = ($2, $4, $1) in (SymbolTable.add sigTable $2 $4 ; ret) }
			| ArgMode Var error		{ doError "expected colon followed by type in signature argument" }
			;

ArgMode			: T_Read	{ READ }
			| T_Write	{ WRITE }
			| T_Read_Write	{ READ_WRITE }
			| error		{ doError "invalid argument mode : expected READ, WRITE, or READ_WRITE" }
			;

VarType			: T_Num_Loop_Counter						{ NUM_LOOP_COUNTER_TYPE }
			| T_Numerical							{ NUM_VAR_TYPE }
			| T_TempNumerical						{ NUM_TMP_VAR_TYPE }
			| T_Symbolic							{ SYM_VAR_TYPE }
			| T_TempSymbolic						{ SYM_TMP_VAR_TYPE }
			| T_NumericalArr						{ NUM_ARRAY_TYPE }
			| T_TempNumericalArr						{ NUM_TMP_ARRAY_TYPE }
			| T_SymbolicArr							{ SYM_ARRAY_TYPE }
			| T_TempSymbolicArr						{ SYM_TMP_ARRAY_TYPE }
			| T_Struct T_LCurlyBracket StructVarList T_RCurlyBracket	{ STRUCT_TYPE($3) }
			| T_Table T_LCurlyBracket TableSignature T_RCurlyBracket	{ NR_TABLE_TYPE($3) }
			| error								{ doError "not a valid variable type" }
			;

StructVarList		: StructVarDeclare StructVarList	{ $1 :: $2 }
			|					{ [] }
			;

StructVarDeclare	: Var T_Colon VarType { ($1,$3) }
			| error		      { doError "error in struct variable declaration" }
			;

TableSignature		: TableSignatureItem				{ [$1] }
			| TableSignatureItem T_Semicolon TableSignature	{ $1 :: $3 }
			;

TableSignatureItem	: T_Identifier T_Colon TableEntryKind							{ ($1,($3,NO_INDEX)) }
			| T_Identifier T_Colon TableEntryKind T_LSquareBracket T_Identifier T_RSquareBracket	{ ($1,($3,
														  match $5 with
														  | "K" -> PRIMARY_INDEX
														  | "k" -> SECONDARY_INDEX
														  | _ -> NO_INDEX))
														}
			| error  { doError "error in table signature item: expected identifier : table entry kind" }
			;

TableEntryKind		: T_Numerical		{ NUMERICAL_ENTRY }
			| T_Symbolic		{ SYMBOLIC_ENTRY }
			| error			{ doError "error in table entry kind: expected numerical or symbolic" }
			;

Bindings		: T_Bindings T_Colon T_LCurlyBracket BindingList T_RCurlyBracket	{ $4 }
			| error									{ doError "error in bindings" }
			;

BindingList		:			{ [] }
			| RealBindingList	{ $1 }
			;

RealBindingList		: Binding					{ [$1] }
			| Binding T_Semicolon RealBindingList		{ $1 :: $3 }
			;

Binding			: Var T_EqualsArrow Var	{ ($1, (!curScope)#mkVariable($3)(SymbolTable.find sigTable $3)) }
			| error			{ doError "error in binding: expected var => var" }
			;

Scope			: T_Scope VarDeclareList	{ !curScope }
			| error 			{ doError "error in scope" }
			;

VarDeclareList		: VarDeclare VarDeclareList	{  }
			|				{  }
			;

VarDeclare		: Var T_Colon VarType { scopeHandleVar $1 $3 }
			;

ProcedureBody		: Code	{ $1 }
			;

Code			: T_LCurlyBracket CommandList T_RCurlyBracket	{ F.mkCode $2 }
			| error						{ doError "error in code" }
			;

OptCode			:			{ None }
			| T_DoubleColon Code	{ Some $2 }
			;

CommandList		:					{ [] }
			| Command T_Semicolon CommandList	{ $1 @ $3 }
			| error T_Semicolon			{ doError "error in command" }
                        ;

Command			: T_Code T_LParen Var T_RParen Code					{ [CODE($3,$5)] }
			| T_Cfg T_LParen Var T_RParen T_LCurlyBracket Cfg T_RCurlyBracket	{ [CFG($3,$6)] }
			| T_Relation Code							{ [RELATION($2)] }
			| T_Transaction BeginTransaction T_LParen Var T_RParen Code OptCode 	{ let ret = [TRANSACTION($4,$6,$7)] in (
														endTransaction() ;
													        ret)
												}
			| T_Breakout_Block Var Code						{ [BREAKOUT_BLOCK($2,$3)] }
			| T_Break Var								{ [BREAK($2)] }
			| T_Goto_Block Code							{ [GOTO_BLOCK($2)] }
			| T_Label Var								{ [LABEL($2)] }
			| T_Goto Var								{ [GOTO($2)] }
			| T_Skip								{ [SKIP] }
			| Equality								{ $1 }
			| T_Abstract_Vars T_LSquareBracket VarList T_RSquareBracket		{ [ABSTRACT_VARS($3)] }
			| T_Assert T_LParen BooleanExpr T_RParen				{ [ASSERT($3)] }
			| T_Branch BranchList							{ [BRANCH($2)] }
			| T_Loop T_When Code T_Exit T_When Code T_Do Code 			{ [LOOP($3,$6,$8)] }
			| T_Operation Var OperationArgList 					{ [OPERATION({op_name=$2;op_args=$3})] }
			| T_Operation Var OperationArgList T_On T_Domains T_LCurlyBracket NameList T_RCurlyBracket	{ [DOMAIN_OPERATION($7,{op_name=$2;op_args=$3})] }
			| T_Call Var T_LParen CallArgList T_RParen 				{ [CALL($2,$4)] }
			| T_Context T_LParen Var T_RParen Code					{ [CONTEXT($3,$5)] }
			| T_Domains T_LParen NameList T_RParen Code				{ [DOMAINS($3,$5)] }
			| T_Insert T_Into Variable T_Values T_LParen InsertTableList T_RParen	{ [INSERT({into=$3;values=$6})] }
			| T_Delete T_Rows T_From Variable T_Where WhereList			{ [DELETE({rows_from=$4;rows_where=$6})] }
			| T_Select SelectList T_From Variable T_Where WhereList			{ [SELECT({selected=$2;from=$4;where=$6})] }
			| Variable T_LSquareBracket Variable T_RSquareBracket T_Equals Variable	{ [(match ($1#getType) with
											            | NUM_ARRAY_TYPE -> ASSIGN_NUM_ELT($1,$3,$6)
												    | SYM_ARRAY_TYPE -> ASSIGN_SYM_ELT($1,$3,$6)
												    | _ -> SKIP
												   )]
												}
			| Variable T_Equals Variable T_LSquareBracket Variable T_RSquareBracket	{ [(match ($3#getType) with
												    | NUM_ARRAY_TYPE -> READ_NUM_ELT($1,$3,$5)
												    | SYM_ARRAY_TYPE -> READ_SYM_ELT($1,$3,$5)
												    | _ -> SKIP
												   )]
												}
			| T_Domain_Cmd T_LParen T_Identifier T_Comma T_Identifier T_Comma T_LSquareBracket DomainCmdArgList T_RSquareBracket T_RParen  { [DOMAIN_CMD($3,$5,$8)] }
			| Variable T_Equals Variable T_Shift T_Num				{ [SHIFT_ARRAY($1,$3,new numerical_t($5))] }
			;

DomainCmdArgList	: DomainCmdArg				{ [$1] }
			| DomainCmdArg T_Comma DomainCmdArgList	{ $1 :: $3 }
			;

DomainCmdArg		: T_Num		{ NUM_DOM_ARG(new numerical_t($1)) }
			| Variable	{ VAR_DOM_ARG($1) }
			;

BeginTransaction	: { beginTransaction(); }
			;

EndTrans		: { }
			;

SelectList		: SelectItem T_Comma SelectList	{ $1 :: $3 }
			| SelectItem			{ [$1] }
			;

SelectItem		: T_Identifier T_As Variable	{ ($1,$3) }
			;

WhereList		: WhereListItem			{ [$1] }
			| WhereListItem T_And WhereList	{ $1 :: $3 }
			;

WhereListItem		: T_Identifier T_Equals Var	{ ($1,getVar $3) }
			;

InsertTableList		: InsertItem				{ [$1] }
			| InsertItem T_Comma InsertTableList	{ $1 :: $3 }
			;

InsertItem		: T_Identifier T_Equals Variable	{ ($1,$3) }
			;

NameList		:		{ [] }
			| RealNameList	{ $1 }
			;

RealNameList		: T_Identifier				{ [$1] }
			| T_Identifier T_Comma RealNameList	{ $1 :: $3 }
			;

CallArgList		:		     { [] }
			| RealCallArgList    { $1 }
			;

RealCallArgList		: CallArg				{ [$1] }
			| CallArg T_Comma RealCallArgList	{ $1 :: $3 }
			;

CallArg			: Var T_EqualsArrow Variable	{ ($1,$3) }
			;

OperationArgList	: T_LParen T_RParen			    { [] }
			| T_LParen RealOperationArgList T_RParen    { $2 }
			;

RealOperationArgList	: OperationArg					{ [$1] }
			| OperationArg T_Comma RealOperationArgList	{ $1 :: $3 }
			;

OperationArg		: T_Identifier T_Colon ArgMode T_EqualsArrow Variable	{ ($1,$5,$3) }
			;

Cfg			: T_Entry T_Colon Var T_Exit T_Colon Var StateList	{ let ret = F.mkCFG_s ($3)($6) in (addCFGStates(ret)($7); ret ) }
			;

StateList		:			{ [] }
			| State StateList	{ $1 :: $2 }
			;

State			: Var T_Colon Code T_Arrow T_LSquareBracket EdgeList T_RSquareBracket	{ ($1,(F.mkState $1 $3),$6) }
			;

EdgeList		:		{ [] }
			| RealEdgeList	{ $1 }
			;

RealEdgeList		: Var				{ [$1] }
			| Var T_Semicolon EdgeList	{ $1 :: $3 }
			;

VarList			: Variable			{ [$1] }
			| Variable T_Comma VarList	{ $1 :: $3 }
			;

Equality		: Variable T_Equals Numerical	{
							  let (commandList,resultExpr) = $3 in
							    if (List.length commandList) = 0 then
								[ASSIGN_NUM($1,resultExpr)]
							    else if !inTransaction then
								commandList@[ASSIGN_NUM($1,resultExpr)]
							    else
								let ret = [TRANSACTION($1#getName,F.mkCode(commandList@[ASSIGN_NUM($1,resultExpr)]),None)] in
								(startedTransaction := false ; !curScope#endTransaction ; ret)
							}
			| Variable T_Equals SymbolicExpr	{ [ASSIGN_SYM($1,$3)] }
			| Variable T_Equals Variable		{
								if (is_array_type ($1#getType)) then
								    [ASSIGN_ARRAY($1,$3)]
								else if (is_struct_type ($1#getType)) then
								    [ASSIGN_STRUCT($1,$3)]
								else if (is_numerical_type ($1#getType)) then
								    [ASSIGN_NUM($1,NUM_VAR($3))]
								else if (is_symbolic_type ($1#getType)) then
								    [ASSIGN_SYM($1,SYM_VAR($3))]
								else
								    [SKIP]
								}

			;

Var			: T_Identifier	{ symbol $1 }
			;

Variable		: Var			{ try getVar $1 with Not_found -> doError ("Variable " ^ $1#getBaseName ^ " does not exist") }
			| Variable T_Hash Var	{ ($1)#field $3 }
			;

BranchList		: Code				{ [$1] }
			| Code T_DoubleVLine BranchList	{ $1 :: $3 }
			;

BooleanExpr		: T_Random							{ RANDOM }
			| T_True							{ TRUE }
			| T_False							{ FALSE }
			| Variable T_GreaterThan Variable				{ GT($1,$3) }
			| Variable T_LessThan Variable					{ LT($1,$3) }
			| Variable T_GreaterThanEqualTo Variable			{ GEQ($1,$3) }
			| Variable T_LessThanEqualTo Variable				{ LEQ($1,$3) }
			| Variable T_Equals Variable					{ EQ($1,$3) }
			| Variable T_NotEqualTo Variable				{ NEQ($1,$3) }
			| Variable T_In T_LCurlyBracket EdgeList T_RCurlyBracket	{ SUBSET($1,$4) }
			| Variable T_Not T_In T_LCurlyBracket EdgeList T_RCurlyBracket	{ DISJOINT($1,$5) }
			| error								{ doError "not a boolean expression" }
			;

Numerical		: T_Num						    { ([],NUM(new numerical_t($1))) }
			| NumericalExpr T_Plus NumericalExpr %prec RootPlus {
										match $1 with (leftList,leftVar) ->
										match $3 with (rightList,rightVar) ->
										(leftList@rightList,PLUS(leftVar,rightVar))
									    }
			| NumericalExpr T_Minus NumericalExpr %prec RootMinus {
										match $1 with (leftList,leftVar) ->
										match $3 with (rightList,rightVar) ->
										(leftList@rightList,MINUS(leftVar,rightVar))
									      }
			| NumericalExpr T_Star NumericalExpr %prec RootMult {
										match $1 with (leftList,leftVar) ->
										match $3 with (rightList,rightVar) ->
										(leftList@rightList,MULT(leftVar,rightVar))
									    }
			| NumericalExpr T_Slash NumericalExpr %prec RootDiv {
										match $1 with (leftList,leftVar) ->
										match $3 with (rightList,rightVar) ->
										(leftList@rightList,DIV(leftVar,rightVar))
									    }
			;

NumericalExpr		: T_Num				                {
									  let _ = handleTransaction() in
									  let temp = (!curScope)#requestNumTmpVariable in
									  ([ASSIGN_NUM(temp,NUM(new numerical_t($1)))],temp)
									}
			| NumericalExpr T_Plus NumericalExpr %prec Plus {
									   let _ = handleTransaction() in
									   let temp = (!curScope)#requestNumTmpVariable in
									   match $1 with (leftList,leftVar) ->
									   match $3 with (rightList,rightVar) ->
									   (leftList@rightList@[ASSIGN_NUM(temp,PLUS(leftVar,rightVar))],temp)
									 }
			| NumericalExpr T_Minus NumericalExpr %prec Minus {
									   let _ = handleTransaction() in
									   let temp = (!curScope)#requestNumTmpVariable in
									   match $1 with (leftList,leftVar) ->
									   match $3 with (rightList,rightVar) ->
									   (leftList@rightList@[ASSIGN_NUM(temp,MINUS(leftVar,rightVar))],temp)
									   }
			| NumericalExpr T_Star NumericalExpr %prec Mult {
									  let _ = handleTransaction() in
									  let temp = (!curScope)#requestNumTmpVariable in
									  match $1 with (leftList,leftVar) ->
									  match $3 with (rightList,rightVar) ->
									  (leftList@rightList@[ASSIGN_NUM(temp,MULT(leftVar,rightVar))],temp)
									}
			| NumericalExpr T_Slash NumericalExpr %prec Div {
									  let _ = handleTransaction() in
									  let temp = (!curScope)#requestNumTmpVariable in
									  match $1 with (leftList,leftVar) ->
									  match $3 with (rightList,rightVar) ->
									  (leftList@rightList@[ASSIGN_NUM(temp,DIV(leftVar,rightVar))],temp)
									}
			| T_LParen NumericalExpr T_RParen		{ $2 }
			| Variable					{ ([],$1) }
			;

SymbolicExpr		: T_Symbol	{ SYM(symbol $1) }
			;

%%
