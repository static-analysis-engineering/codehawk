open CHPretty
open CHLanguage

type t =
  | True 
  | VarInt of (int * int option * int option) (* vid; val *)
  | VarNull of int

let null_var_cstr = "null-var"
let var_int_cstr = "var-int"
let true_cstr = "tt"
let encode_bound = function
| None -> "inf"
| Some i -> string_of_int i

let decode_bound = function
| "inf" -> None
| s -> Some(int_of_string s)

let from_symbol (sym: symbol_t): t option =
  match sym#getSymbol with
  | [s] ->
    begin 
      match String.split_on_char ':' s with
      | [k; v] when k = null_var_cstr -> Some (VarNull (int_of_string v))
      | [k; v; l; u] when k = var_int_cstr -> 
        let lb = decode_bound l in
        let ub = decode_bound u in
        Some (VarInt (int_of_string v, lb, ub))
      | [k] when k = true_cstr-> Some True
      | _ -> None (* these should throw*)
    end
  | _ -> None

let to_symbol: t -> symbol_t = function
  | True -> new symbol_t true_cstr
  | VarNull i -> new symbol_t (null_var_cstr ^ ":" ^ string_of_int i)
  | VarInt (v, l, u) -> 
    let lb = encode_bound l in
    let ub = encode_bound u in
    new symbol_t (var_int_cstr ^ ":" ^ string_of_int v ^ ":" ^ lb ^ ":" ^ ub)

let to_pretty = function
| True -> STR "T"
| VarNull i -> LBLOCK [ STR "Null("; INT i; STR ")" ]
| VarInt (v, l, u) -> 
  LBLOCK [ STR "VarRange("; INT v; STR ", "; STR (encode_bound l); STR ", "; STR (encode_bound u);  STR ")"]
