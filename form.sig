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
| Quant of string * string * sort * form
| fVar of string;
exception ERR of string
val TRUE: form
val FALSE: form
val mk_ob: string -> term
val mk_ar: string -> string -> string -> term
val mk_neg: form -> form
val mk_conj: form -> form -> form
val mk_disj: form -> form -> form
val mk_imp: form -> form -> form
val mk_dimp: form -> form -> form
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
val mk_all:  string -> sort -> form -> form
val mk_exists: string -> sort -> form -> form
val pair_compare: ('a * 'b -> order) -> ('c * 'd -> order) -> ('a * 'c) * ('b * 'd) -> order
val sort_compare: sort * sort -> order
val term_compare: term * term -> order
type menv
val match_term: term -> term -> menv -> menv
val match_sort: sort -> sort -> menv -> menv
val match_tl: term list -> term list -> menv -> menv
val match_form: form -> form -> menv -> menv
val strip_all: form -> form
val strip_ALL: form -> form * (string * sort) list
val pvariantt: (string * sort) set -> term -> term
val inst_fVar: string * form -> form -> form
val inst_fVarl: (string * form) list -> form -> form
val inst_fVare: menv -> form -> form
end

