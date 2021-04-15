signature thm = 
sig
type form = form.form
type term = term.term
type sort = term.sort
type menv = form.menv
datatype thm = thm of form list * form
val assume: form -> thm
val refl: term -> thm
val concl: thm -> form
val trans: thm -> thm -> thm
val sym: thm -> thm
val ant: thm -> form list
val inst1:  thm -> (string * form) -> thm
val inst: thm -> menv -> thm
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
val existsE: thm -> (string * sort) -> thm
val existsI: thm -> (string * sort) -> term -> form -> thm
val simple_exists: (string  * sort) -> thm -> thm
val falseE: form -> thm
val trueI: form list -> thm
val allI: (string * sort) -> thm -> thm
val allE: thm -> term -> thm
val disch: form -> thm -> thm
val mp: thm -> thm -> thm
val undisch: thm -> thm
val add_assum: form -> thm -> thm
val imp_trans: thm -> thm -> thm
val frefl: form -> thm
val dimpl2r: thm -> thm
val dimpr2l: thm -> thm
val iff_trans: thm -> thm -> thm
val equivT: thm -> thm

val conj_iff: thm -> thm -> thm
val disj_iff: thm -> thm -> thm
val imp_iff: thm -> thm -> thm
val dimp_iff: thm -> thm -> thm
val all_iff: thm -> (string * sort) -> thm
val exists_iff: thm -> (string * sort) -> thm

val T_conj_1: thm
val T_conj_2: thm 
val F_conj_1: thm
val F_conj_2: thm

val T_disj_1: thm
val T_disj_2: thm
val F_disj_1: thm
val F_disj_2: thm

val T_imp_1: thm
val T_imp_2: thm
val F_imp_1: thm
val F_imp_2: thm

val T_dimp_1: thm
val T_dimp_2: thm
val F_dimp_1: thm
val F_dimp_2: thm

val all_true_ob: thm
val all_true_ar: thm

val all_false_ob: thm
val all_false_ar: thm


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
(*type thm*)
(*rules for inference*) 
end
