signature drule = 
sig
type form = form.form
type term = term.term
type sort = term.sort
type menv = form.menv
type thm = thm.thm
val simple_exists: (string  * sort) -> thm -> thm
val imp_trans: thm -> thm -> thm
val frefl: form -> thm
val dimpl2r: thm -> thm
val dimpr2l: thm -> thm
val iff_trans: thm -> thm -> thm
val equivT: thm -> thm

val dimp_mp_l2r: thm -> thm -> thm
val dimp_mp_r2l: thm -> thm -> thm


val abstl: thm -> (string * sort) list -> thm
val spec_all: thm -> thm
val specl: thm -> term list -> thm

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

val exists_true_ar: thm
val exists_true_ob: thm
val exists_false_ar: thm 
val exists_false_ob: thm

val imp_canon: thm -> thm list
val fconv_canon: thm -> thm list

(*type thm*)
(*rules for inference*) 
end
