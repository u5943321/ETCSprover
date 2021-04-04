signature form = 
sig
type sort = term.sort
type term = term.term
(*datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * sort * (string * sort) list
    | Bound of int
    | Fun of string * sort * term list;
*)
datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;
val TRUE: form
val FALSE: form
val dest_eq: form -> term * term
val is_eqn: form -> bool
val eq_form: form * form -> bool
val substt: (string * sort) * term -> term -> term
val substs: (string * sort) * term -> sort -> sort
val substf: (string * sort) * term -> form -> form
val fvf: form -> (string * sort) list
val fvfl: form list -> (string * sort) list
val subst_bound: term -> form -> form
val abstract: string * sort -> form -> form
val match_term0: term -> term -> (string,term) Binarymap.dict -> (string,term) Binarymap.dict
val match_sort0: sort -> sort -> (string,term) Binarymap.dict -> (string,term) Binarymap.dict
val match_tl: term list -> term list -> (string,term) Binarymap.dict -> (string,term) Binarymap.dict
val match_form: form -> form -> (string,term) Binarymap.dict -> (string,term) Binarymap.dict
val strip_all: form -> form
exception ERR of string
val inst_term: (string,term) Binarymap.dict -> term -> term
val inst_sort: (string,term) Binarymap.dict -> sort -> sort
val inst_form: (string,term) Binarymap.dict -> form -> form
end

