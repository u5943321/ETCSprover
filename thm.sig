signature thm = 
sig
type form = form.form
type term = term.term
type sort = term.sort
type menv = form.menv
datatype thm = thm of (string * sort) set * form list * form
val ant: thm -> form list
val cont: thm -> (string * sort) set
val assume: form -> thm
val concl: thm -> form

val eq_thm: thm -> thm -> bool

val refl: term -> thm

val trans: thm -> thm -> thm
val sym: thm -> thm
val mk_sss: (string * sort) set list -> (string * sort) set
val inst_thm: menv -> thm -> thm
val conjI: thm  -> thm -> thm
val disjI1: thm -> form -> thm
val disjI2: form -> thm -> thm
val dimpI: thm -> thm -> thm
val dimpE: thm -> thm
val EQ_fsym: string -> sort -> thm list -> thm
val EQ_psym: string -> thm list -> thm
val conjE1: thm -> thm
val conjE2: thm -> thm
val disjE: form -> form -> form -> thm -> thm -> thm -> thm
val tautI: form -> thm
val negI: thm -> form -> thm
val negE: thm -> thm -> thm
val existsE: string * sort -> thm -> thm -> thm
val existsI: thm -> (string * sort) -> term -> form -> thm
val falseE: form list -> form -> thm
val trueI: form list -> thm
val allI: (string * sort) -> thm -> thm
val allE: thm -> term -> thm
val disch: form -> thm -> thm
val mp: thm -> thm -> thm
val add_cont: thm -> (string * sort) set -> thm




val define_pred: form -> thm
val define_fun: form -> thm


val idL: thm
val idR: thm
val o_assoc: thm
val ax1_1: thm
val ax1_2: thm
val ax1_3: thm
val ax1_4: thm
val ax1_5: thm
val ax1_6: thm
val ax2: thm
val ax3: thm
val ax4: thm
val ax5: thm
val ax6: thm
val ax7: thm
val ax8: thm


(*type thm*)
(*rules for inference*) 
end
