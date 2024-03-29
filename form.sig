signature form = 
sig
type sort = term.sort
type term = term.term
type form 
datatype form_view =
    vConn of string * form list
  | vQ of string * string * sort * form
  | vPred of string * term list
  | vfVar of string

val view_form: form -> form_view

(*exception ERR of string * sort list * term list * 'a list  *)

exception ERR of string * sort list * term list * form list 
val simple_fail: string -> exn
val wrap_err: string -> exn -> exn


val eq_forml: form list -> form list -> bool
val fmem: form -> form list -> bool
val ril: form -> form list -> form list
val is_conj: form -> bool
val is_disj: form -> bool
val is_imp: form -> bool
val is_dimp: form -> bool
val is_neg: form -> bool
val is_forall: form -> bool
val is_exists: form -> bool
val is_quant: form -> bool
val is_eq: form -> bool

val TRUE: form
val FALSE: form
val mk_ob: string -> term
val mk_ar: string -> term -> term -> term
val mk_ar0: string -> string -> string -> term
val mk_conn: string -> form list -> form
val mk_neg: form -> form
val mk_conj: form -> form -> form
val mk_disj: form -> form -> form
val mk_imp: form -> form -> form
val mk_dimp: form -> form -> form
val mk_forall:  string -> sort -> form -> form
val mk_exists: string -> sort -> form -> form
val mk_quant: string -> string -> sort -> form -> form
val mk_pred: string -> term list -> form
val mk_P0: string -> term list -> form
val mk_fvar: string -> form
val mk_eq: term -> term -> form

val dest_eq: form -> term * term
val dest_imp: form -> form * form
val dest_dimp: form -> form * form
val dest_neg: form -> form
val dest_conj: form -> form * form
val dest_disj: form -> form * form
val dest_pred: form -> string * term list
val dest_exists: form -> (string * sort) * form
val dest_forall: form -> (string * sort) * form

val eq_form: form * form -> bool
val substf: (string * sort) * term -> form -> form

val fvf: form -> (string * sort) set
val fvfl: form list -> (string * sort) set
val subst_bound: term -> form -> form
val abstract: string * sort -> form -> form

type vd = term.vd
type fvd
type menv

val vd_of: menv -> vd
val fvd_of: menv -> fvd
val mempty: menv
val pmenv: menv -> ((string * sort) * term) list * (string * form) list

val emptyfvd: fvd
val lookup_f: fvd -> string -> form option


val mk_fenv: (string * form) list -> fvd
val mk_inst: ((string * sort) * term) list -> (string * form) list -> menv
val mk_menv: vd -> fvd -> menv

(*
val match_term: (string * sort) set -> term -> term -> menv -> menv
val match_sort: (string * sort) set -> sort -> sort -> menv -> menv
val match_tl: (string * sort) set -> term list -> term list -> menv -> menv
*)

val match_form: (string * sort) set -> form -> form -> menv -> menv
val strip_forall: form -> form * (string * sort) list
val strip_exists: form -> form * (string * sort) list
val strip_quants: form -> form * (string * sort) list


val fsymsf: form -> string set
val psymsf: form -> string set

(*
val string_of_form: form -> string
*)
(*
val inst_sort: menv -> sort -> sort
val inst_term: menv -> term -> term
*)

val inst_form: menv -> form -> form

val is_wfmenv: menv -> bool
val ok_dpdc: menv -> (string * sort) * term -> bool

val dest_forall0: form -> string * string * sort * form
end

