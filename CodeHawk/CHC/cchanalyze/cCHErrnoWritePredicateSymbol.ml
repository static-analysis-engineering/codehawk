open CHPretty
open CHLanguage

type t =
  | True 
  | VarNull of int
let from_symbol (sym: symbol_t): t option =
  match sym#getSymbol with
  | [s] ->
    begin 
      match String.split_on_char ':' s with
      | ["null-var"; v] -> Some (VarNull (int_of_string v))
      | ["tt"] -> Some True
      | _ -> None (* these should throw*)
    end
  | _ -> None

let to_symbol: t -> symbol_t = function
  | True -> new symbol_t "tt"
  | VarNull i -> new symbol_t ("null-var:" ^ string_of_int i)

let to_pretty = function
| True -> STR "T"
| VarNull i -> LBLOCK [ STR "Null("; INT i; STR ")" ]
