open CHPretty
open CHLanguage

type t =
  | True 
  | VarEqVal of (int * int) (* vid; val *)
  | VarNull of int
let from_symbol (sym: symbol_t): t option =
  match sym#getSymbol with
  | [s] ->
    begin 
      match String.split_on_char ':' s with
      | ["null-var"; v] -> Some (VarNull (int_of_string v))
      | ["eq-const"; v; i] -> Some (VarEqVal (int_of_string v, int_of_string i))
      | ["tt"] -> Some True
      | _ -> None (* these should throw*)
    end
  | _ -> None

let to_symbol: t -> symbol_t = function
  | True -> new symbol_t "tt"
  | VarNull i -> new symbol_t ("null-var:" ^ string_of_int i)
  | VarEqVal (v, i) -> new symbol_t ("eq-const:" ^ string_of_int v ^ ":" ^ string_of_int i)

let to_pretty = function
| True -> STR "T"
| VarNull i -> LBLOCK [ STR "Null("; INT i; STR ")" ]
| VarEqVal (v, i) -> LBLOCK [ STR "EqConst("; INT v; STR ", "; INT i; STR ")"]
