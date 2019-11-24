{
(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: A. Cody Schuffelen
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

   open Parser        (* The type token is defined in parser.mli *)
   open CHNumerical
   exception Eof
	
   let incr_linenum n lexbuf =
	let pos = lexbuf.Lexing.lex_curr_p in
	lexbuf.Lexing.lex_curr_p <- { pos with
	Lexing.pos_lnum = pos.Lexing.pos_lnum + n;
	Lexing.pos_bol = pos.Lexing.pos_cnum;
	}

    let getLineIncr s = 
	let rec f str lines sp = 
	let nr = try String.index_from str sp '\n'
			with Not_found -> -1 in
	if (nr > 0) then f str (lines+1) (nr+1) else lines in
	f s 0 0 

}

let identifier = [ '_' 'a'-'z' 'A'-'Z'] [ '_' 'a'-'z' 'A'-'Z' '\'' '0' - '9' ]*
let num = '-'?[ '0' - '9' ]+
let singleStr = '\'' [^ '\'' ]* '\''
let untermSingleStr = '\'' [^ '\'']*

rule token = parse
		[' ' '\t' ]     	{ token lexbuf }     (* skip blanks *)
	|	'\n'				{ (incr_linenum 1 lexbuf ; token lexbuf) }
	|	"PROCEDURE"			{ T_Procedure }
	|	"TRANSACTION"		{ T_Transaction }
	|	"BINDINGS"			{ T_Bindings }
	|	"SCOPE"				{ T_Scope }
	|	"EXIT"				{ T_Exit }
	|	"LOOP"				{ T_Loop }
	|	"WHEN"				{ T_When }
	|	"ASSERT"			{ T_Assert }
	|	"NUMERICAL"			{ T_Numerical }
	|	"NUMERICAL[]"		{ T_NumericalArr }
	|	"T_NUMERICAL"		{ T_TempNumerical }
	|	"T_NUMERICAL[]"		{ T_TempNumericalArr }
	|	"NUM_LOOP_COUNTER"	{ T_Num_Loop_Counter }
	|	"SYMBOLIC"			{ T_Symbolic }
	|	"SYMBOLIC[]"		{ T_SymbolicArr }
	|	"T_SYMBOLIC"		{ T_TempSymbolic }
	|	"T_SYMBOLIC[]"		{ T_TempSymbolicArr }
	|	"OPERATION"			{ T_Operation }
	|	"CFG"				{ T_Cfg }
	|	"ENTRY"				{ T_Entry }
	|	"EXIT"				{ T_Exit }
	|	"GOTO"				{ T_Goto }
	|	"GOTO_BLOCK"		{ T_Goto_Block }
	|	"BREAK"				{ T_Break }
	|	"BREAKOUT_BLOCK"	{ T_Breakout_Block }
	|	"SKIP"				{ T_Skip }
	|	"LABEL"				{ T_Label }
	|	"TABLE"				{ T_Table }
	|	"DOMAINS"			{ T_Domains }
	|	"DOMAIN_CMD"		{ T_Domain_Cmd }
	|	"READ"				{ T_Read }
	|	"WRITE"				{ T_Write }
	|	"READ/WRITE"		{ T_Read_Write }
	|	"STRUCT"			{ T_Struct }
	|	"CODE"				{ T_Code }
	|	"RELATION"			{ T_Relation }
	|	"ABSTRACT_VARS"		{ T_Abstract_Vars }
	|	"ABSTRACT_ELTS"		{ T_Abstract_Elts }
	|	"BRANCH"			{ T_Branch }
	|	"CONTEXT"			{ T_Context }
	|	"CALL"				{ T_Call }
	|	"MOVE_VALUES"		{ T_Move_Values }
	|	"OF"				{ T_Of }
	|	"ON"				{ T_On }
	|	"MOVE_RELATIONS"	{ T_Move_Relations }
	|	"OVER"				{ T_Over }
	|	"SELECT"			{ T_Select }
	|	"INSERT"			{ T_Insert }
	|	"INTO"				{ T_Into }
	|	"VALUES"			{ T_Values }
	|	"DELETE"			{ T_Delete }
	|	"ASSIGN_TABLE"		{ T_Assign_Table }
	|	"DO"				{ T_Do }
	|	"RANDOM"			{ T_Random }
	|	"TRUE"				{ T_True }
	|	"FALSE"				{ T_False }
	|	"IN"				{ T_In }
	|	"NOT"				{ T_Not }
	|	"ROWS"				{ T_Rows }
	|	"WHERE"				{ T_Where }
	|	"FROM"				{ T_From }
	|	"AND"				{ T_And }
	|	"AS"				{ T_As }
	
	|	'('					{ T_LParen }
	|	')'					{ T_RParen }
	|	'{'					{ T_LCurlyBracket }
	|	'}'					{ T_RCurlyBracket }
	|	'['					{ T_LSquareBracket }
	|	']'					{ T_RSquareBracket }
	|	':'					{ T_Colon }
	|	'='					{ T_Equals }
	|	"=>"				{ T_EqualsArrow }
	|	"->"				{ T_Arrow }
	|	'+'					{ T_Plus }
	|	'-'					{ T_Minus }
	|	'*'					{ T_Star }
	|	'/'					{ T_Slash }
	|	"||"				{ T_DoubleVLine }
	|	"::"				{ T_DoubleColon }
	|	'>'					{ T_GreaterThan }
	|	"<<"				{ T_Shift }
	|	'<'					{ T_LessThan }
	|	">="				{ T_GreaterThanEqualTo }
	|	"<="				{ T_LessThanEqualTo }
	|	"=="				{ T_EqualTo }
	|	"!=" 				{ T_NotEqualTo }
	|	','					{ T_Comma }
	|	';'					{ T_Semicolon }
	|	'#'					{ T_Hash }
	
	|	'\'' (([^ '\'' ]*) as sym)  '\''	{ T_Symbol(sym) }
	|	num as number		{ T_Num(Big_int_Z.big_int_of_string(number)) }
	|	identifier as str	{ T_Identifier(str) }
	|	eof					{ T_Eof }


{}
