## CodeHawk OCaml Programming Style Guide

Loosely based on the guidelines given on the
[Ocaml.org](https://ocaml.org/learn/tutorials/guidelines.html)
website.

### Page layout

#### Width of the page
A page is 80 columns wide. Except in rare cases all lines should be 80 characters
or less including indentation.

#### Height of a page
A function should ideally not exceed a single screen page (about 70 lines). This
especially applies to functions with complex control flow that include imperative
constructs. Exceptions can be made for functions that consist of a single pattern
matching construct with many clauses.

#### Indentation

- **width**: indentation is 2 spaces
- **if-then-else**: Except for very short statements a branch is written as
<pre>
if cond then
&nbsp; statement1
else
&nbsp; statement2
</pre>
- **sequence**: A sequence of more than one statement should be enclosed in
a begin-end, which is to be written as:
<pre>
begin
&nbsp; statement1 ;
&nbsp; statement2 ;
&nbsp; ...
end
</pre>
  A very short sequence may be written on one line as
  <pre>
  begin stmt1 ; stmt2 end
  </pre>
  Composite statements that are part of a sequence such as if-then statements or
  pattern match statements should be enclosed in parentheses, e.g.,
  <pre>
  begin
  &nbsp; (if p then a := 3);
  &nbsp; (match x with
  &nbsp; &nbsp;| 3 -> p ()
  &nbsp; &nbsp;| 4 -> q ()
  &nbsp; &nbsp;| _ -> z x) ;
  &nbsp; r
  end
  </pre>
- **function/method parameters**:
  If the function name and all of the parameters and the result type fit within 80 characters:
  <pre>
  let fname (p1:t1) (p2:t2):t3 =
  </pre>
  otherwise if all of the parameters and the result type fit on one line:
  <pre>
  let fname
  &nbsp; &nbsp; &nbsp; (p1:t1) (p2:t2) .... :t3 =
  </pre>
  otherwise each parameter should be on on a separate line:
  <pre>
  let fname
  &nbsp; &nbsp; &nbsp; (p1:t1)
  &nbsp; &nbsp; &nbsp; (p2:t2)
  &nbsp; &nbsp; &nbsp; (p3:t3)
  &nbsp; &nbsp; &nbsp; ...
  &nbsp; &nbsp; &nbsp; (pn:tn):resulttype =
  </pre>
- **function/method call arguments**:
  if the receiving variable, function name and all of the arguments fit within the 80 character limit:
  <pre>
  let x = fname arg1 aarg2 arg3 in
  </pre>
  otherwise, if the function name and  all of the arguments fit within the 80 character limit:
  <pre>
  let longvariablename =
  &nbsp fname arg1 arg2 ..... in
  </pre>
  otherwise each argument should be on a separate line:
  <pre>
  let x =
  &nbsp; fname
  &nbsp; &nbsp; arg1
  &nbsp; &nbsp; arg2
  &nbsp; &nbsp; ...
  &nbsp; &nbsp; argn in
  </pre>
- **pattern matching constructs**:
  All clauses should start with a vertical bar, including the first one. Short
  result expressions may be written on the same line. Multiple-line result
  expressions are indented by 2 spaces:
  <pre>
  match v with
  | case1 -> e1
  | othercase2 ->
  &nbsp; &nbsp; longexpression_or_multiple-line expression
  | ...
  </pre>
  Nested pattern matching constructs should be enclosed with begin-end:
  <pre>
  match v with
  | case1 ->
  &nbsp; &nbsp; begin
  &nbsp; &nbsp; &nbsp; match w with
  &nbsp; &nbsp; &nbsp; | ... -> ...
  &nbsp; &nbsp; &nbsp; | ... -> ...
  &nbsp; &nbsp; end
  | ... -> ...
  </pre>
  or in parentheses:
  <pre>
  | case1 ->
  &nbsp; &nbsp; (match w with
  &nbsp; &nbsp; &nbsp;| ... -> ...
  &nbsp; &nbsp; &nbsp;| ... -> ... )
  | ... -> ...
  </pre>
- **operators**: Expressions that do not fit within the 80 character limit are to be
  split such that the operator is the first character on the new line:
  <pre>
  let x = longname1
  &nbsp; &nbsp; &nbsp; &nbsp; + longname2
  &nbsp; &nbsp; &nbsp; &nbsp; + longname3
  &nbsp; &nbsp; &nbsp; &nbsp; + ... in
  </pre>
  and similar for conditional expressions:
  <pre>
  if longconditon1
  &nbsp; &nbsp;&& longcondition2
  &nbsp; &nbsp;&& ... then
  </pre>
- **function/method signatures**: If the signature fits within the 80-character limit:
  <pre>
  val fname: t1 -> t2 -> t3 -> t4 -> ....
  </pre>
  otherwise, if the types fit within the 80-character limit:
  <pre>
  val fname:
  &nbsp; t1 -> t2 -> t3 -> t4 -> ...
  </pre>
  otherwise, all types are to be written on a separate line, with leading arrows (or
  asterisks) for all but the first type:
  <pre>
  val fname:
  &nbsp; t1
  &nbsp; -> t2
  &nbsp; -> t3
  &nbsp; -> t4
  &nbsp; -> t5
  &nbsp; &nbsp; &nbsp;* ...
  </pre>
  
### Naming conventions

#### Module names
Module names in class, function, or variable names are discouraged, as they tend
to cause more lines to be split up. Modules should be opened at the top of the
file, organized by subsystem, in alphabetical order per subsystem, e.g.,
<pre>
(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHLogger
open CHXmlDocument
</pre>
In most of the CodeHawk subsystems most of the fundamental types are collected in
a single mli file, e.g. in CHB/bchlib/bCHLibTypes.mli, and in
CHB/bchlibx86/bCHLibx86Types.mli, so only one file needs to be opened.

#### Type names
Class interface types should be lower-case snake case and have suffix _int,
e.g., domain_int. Class types and other types should be lower-case snake
case and have suffix _t, e.g., pretty_t.

#### Function names
Function names should be lower-case snake case, that is, words separated by
underscores, like has_bound or get_first_element. 

#### Variable names
Variable names must start with a lower-case character (OCaml requirement), but
may otherwise be snakecase or camelcase. Some subsystems have some additional
conventions on the naming of variables of a particular type, to make them easier
to recognize as such, e.g., floc in the binary analyzer (CHB) or mInfo in the
java analyzer (CHJ); these are described per subsystem.
