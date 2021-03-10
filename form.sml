structure form :> form = 
struct
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
end
