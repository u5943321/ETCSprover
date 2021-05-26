signature term = 
sig
datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Bound of int
    | Fun of string * sort * term list;

exception ERR of string

val enclose: string -> string
val conc_list: string -> string list -> string
val conc_list1: string -> string list -> string
val string_of_sort: sort -> string
val string_of_term: term -> string
val string_of_tl: term list -> string


val sort_of: term -> sort
val mk_ar_sort: term -> term -> sort
val mk_ob: string -> term
val mk_ar:string -> term -> term -> term
val mk_ar0: string -> string -> string -> term
val mk_var: string -> sort -> term
val mk_fun: string -> sort -> term list -> term 
val mk_const: string -> sort -> term

val is_var: term -> bool

val dest_fun: term -> string * sort * term list
val dest_var: term -> string * sort


end

