signature term = 
sig
type sort
type term

datatype sort_view = 
         vo
         | va of term * term

datatype term_view =
    vVar of string * sort
  | vB of int
  | vFun of string * sort * term list

val view_sort: sort -> sort_view
val view_term: term -> term_view

val eq_term: term * term -> bool
val eq_sort: sort * sort -> bool

exception TER of string * sort list * term list
(*
val enclose: string -> string
val conc_list: string -> string list -> string
val conc_list1: string -> string list -> string
val string_of_sort: sort -> string
val string_of_term: term -> string
val string_of_tl: term list -> string
*)

val mk_ob_sort: sort
val mk_ar_sort: term -> term -> sort

val mk_var: string -> sort -> term
val var: string * sort -> term
val mk_fun: string -> term list -> term 
val mk_bound: int -> term

val sort_of: term -> sort

val mk_ob: string -> term
val mk_ar:string -> term -> term -> term
val mk_ar0: string -> string -> string -> term

val mk_const: string -> sort -> term

val is_var: term -> bool

val dest_fun: term -> string * sort * term list
val dest_var: term -> string * sort
val dest_ar: sort -> term * term

(*
val dest_pair: term -> term * term
val dest_o: term -> term * term
*)


val one: term
val s: term
val z: term
val zero: term
val N: term

(*
val to1: term -> term
val tp: term -> term
val id: term -> term

val p1: term -> term -> term
val p2: term -> term -> term
val pa: term -> term -> term
val po: term -> term -> term
val i1: term -> term -> term
val i2: term -> term -> term

val O: term * term -> term
val cod: sort -> term
val coeqa: term -> term -> term
val coeqo: term -> term -> term
val copa: term -> term -> term
val copo: term -> term -> term
*)

val replaces: term * term -> sort -> sort
val replacet: term * term -> term -> term

val substs: (string * sort) * term -> sort -> sort
val substt: (string * sort) * term -> term -> term 

val fvt: term -> (string * sort) set
val fvtl: term list -> (string * sort) set
val fvs: sort -> (string * sort) set

val pair_compare: ('a * 'b -> order) -> ('c * 'd -> order) -> ('a * 'c) * ('b * 'd) -> order
val sort_compare: sort * sort -> order
val term_compare: term * term -> order
val essps: (string * sort) set
val pvariantt: (string * sort) set -> term -> term

val fsymss: sort -> string set
val fsymst: term -> string set

datatype ForP = fsym | psym
val fxty: string -> int
val is_const: string -> bool
val fpdict: (string, ForP) Binarymap.dict ref
val fpdict0: (string, ForP) Binarymap.dict
val insert_fsym: string -> unit
val insert_psym: string -> unit


type fsymd = (string, sort * (string * sort) list) Binarymap.dict
val fsyms0: fsymd
val fsyms: fsymd ref
val lookup_fun: fsymd -> string -> (sort * (string * sort) list) option
val is_fun: string -> bool
val new_fun:
   string -> sort * (string * sort) list -> unit




type psymd = (string, (string * sort) list) Binarymap.dict
val psyms0: psymd
val psyms: psymd ref
val lookup_pred: psymd -> string -> (string * sort) list option
val is_pred: string -> bool
val new_pred:
   string -> (string * sort) list -> unit

type vd
val emptyvd:vd
val mk_tenv: ((string * sort) * term) list -> vd
val v2t: string * sort -> term -> vd -> vd
val lookup_t: vd -> string * sort -> term option
val match_term: (string * sort) set -> term -> term -> vd -> vd
val match_sort: (string * sort) set -> sort -> sort -> vd -> vd
val match_tl: (string * sort) set -> term list -> term list -> vd -> vd
val pvd: vd -> ((string * sort) * term) list

val inst_sort: vd -> sort -> sort
val inst_term: vd -> term -> term
end

