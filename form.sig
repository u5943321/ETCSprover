signature form = 
sig
datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * sort * (string * sort) list
    | Bound of int
    | Fun of string * sort * term list;

datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;

val eq_form : form * form -> bool
val substt: (string * sort) * term -> term -> term
val substs: (string * sort) * term -> sort -> sort
val substf: (string * sort) * term -> form -> form
end

