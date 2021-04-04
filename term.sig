signature term = 
sig
datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    (*| Param of string * sort * (string * sort) list *)
    | Bound of int
    | Fun of string * sort * term list;

val sort_of: term -> sort
end

