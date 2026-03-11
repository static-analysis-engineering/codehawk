open CHPretty
open CHLanguage 

type t =
  | True 
  | VarNull of int

val from_symbol : symbol_t -> t option

val to_symbol : t -> symbol_t

val to_pretty : t -> pretty_t