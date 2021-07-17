signature logic = 
sig
type form = form.form
type term = term.term
type sort = term.sort
type menv = form.menv
type thm

datatype thm_view = vth of ((string * sort) set * form list * form) 

val dest_thm: thm -> (string * sort) set * form list * form
val view_thm: thm -> thm_view
val mk_thm: (string * sort) set -> form list -> form -> thm

val eq_thm: thm -> thm -> bool

val ant: thm -> form list
val concl: thm -> form
val cont: thm -> (string * sort) set

val assume: form -> thm

val refl: term -> thm
val trans: thm -> thm -> thm
val sym: thm -> thm

val mk_sss: (string * sort) set list -> (string * sort) set
val inst_thm: menv -> thm -> thm

val EQ_fsym: string -> thm list -> thm
val EQ_psym: string -> thm list -> thm

val conjI: thm  -> thm -> thm
val conjE1: thm -> thm
val conjE2: thm -> thm

val disjI1: form -> thm -> thm
val disjI2: form -> thm -> thm
val disjE: thm -> thm -> thm -> thm

val dimpI: thm -> thm -> thm
val dimpE: thm -> thm

val tautI: form -> thm

val negI: form -> thm -> thm
val negE: thm -> thm -> thm

val existsE: string * sort -> thm -> thm -> thm
val existsI: string * sort -> term -> form -> thm -> thm
val falseE: form list -> form -> thm
val trueI: form list -> thm
val allI: (string * sort) -> thm -> thm
val allE: term -> thm -> thm
val disch: form -> thm -> thm
val mp: thm -> thm -> thm
val add_cont: (string * sort) set -> thm -> thm

 
end
