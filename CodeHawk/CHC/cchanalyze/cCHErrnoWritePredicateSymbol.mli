open CHPretty
open CHLanguage 

type t =
  | True 
  | VarEqVal of (int * int) (* vid; val *)
  | VarNull of int

val from_symbol : symbol_t -> t option

val to_symbol : t -> symbol_t

val to_pretty : t -> pretty_t