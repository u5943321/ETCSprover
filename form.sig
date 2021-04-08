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
val mk_neg: form -> form
val dest_eq: form -> term * term
val dest_imp: form -> form * form
val dest_iff: form -> form * form
val is_all: form -> bool
val is_eqn: form -> bool
val eq_form: form * form -> bool
val substt: (string * sort) * term -> term -> term
val substs: (string * sort) * term -> sort -> sort
val substf: (string * sort) * term -> form -> form
val fvf: form -> (string * sort) set
val fvfl: form list -> (string * sort) set
val subst_bound: term -> form -> form
val abstract: string * sort -> form -> form
val pair_compare: ('a * 'b -> order) -> ('c * 'd -> order) -> ('a * 'c) * ('b * 'd) -> order
val sort_compare: sort * sort -> order
val term_compare: term * term -> order
val match_term0: term -> term -> ((string * sort),term) Binarymap.dict -> ((string * sort),term) Binarymap.dict 
val match_sort0: sort -> sort -> ((string * sort),term) Binarymap.dict -> ((string * sort),term) Binarymap.dict
val match_tl: term list -> term list -> ((string * sort),term) Binarymap.dict -> ((string * sort),term) Binarymap.dict
val match_form: form -> form -> ((string * sort),term) Binarymap.dict -> ((string * sort),term) Binarymap.dict
val strip_all: form -> form
exception ERR of string
val inst_term: ((string * sort),term) Binarymap.dict -> term -> term
val inst_sort: ((string * sort),term) Binarymap.dict -> sort -> sort
val inst_form: ((string * sort),term) Binarymap.dict -> form -> form
val strip_ALL: form -> form * (string * sort) list
val pvariantt: (string * sort) set -> term -> term
end

