signature tactic = 
sig
type tactic = abbrev.tactic
type fconv = abbrev.fconv
type thm_tactic = abbrev.thm_tactic
val >> : (tactic * tactic) -> tactic
val >-- : (tactic * tactic) -> tactic

val empty: 'a -> 'b list -> 'a
val accept_tac: thm_tactic
val assume_tac: thm_tactic
val conj_tac: tactic
val disj1_tac: tactic
val disj2_tac: tactic
val contra_tac: tactic
val ccontra_tac: tactic
val imp_tac: tactic
val dimp_tac: tactic
val wexists_tac: term -> tactic
val gen_tac: tactic
val then_tac: (tactic * tactic) -> tactic
val then1_tac: (tactic * tactic) -> tactic
val Orelse: (tactic * tactic) -> tactic
val stp_tac: tactic
val all_tac: tactic
val repeat: tactic -> tactic 
val assum_list: (thm.thm list -> tactic) -> tactic
val pop_assum_list: (thm.thm list -> tactic) -> tactic
val pop_assum: thm_tactic -> tactic
val mp_tac: thm_tactic
val rw_tac: thm.thm list -> tactic
val T_INTRO_TAC: tactic
val drule: thm_tactic
val arw_tac: thm.thm list -> tactic
val once_arw_tac: thm.thm list -> tactic
val fconv_tac: fconv -> tactic
val once_rw_tac: thm.thm list -> tactic
val valid: tactic -> tactic
val by_tac: form.form -> tactic
val suffices_tac: form.form -> tactic
val match_mp_tac: thm_tactic
val rule_assum_tac: (thm.thm -> thm.thm) -> tactic
val choose_tac: string -> form.form -> tactic

val every: tactic list -> tactic
val map_every: ('a -> tactic) -> 'a list -> tactic

val CONTR_TAC:thm_tactic
val first: tactic list -> tactic
val check_assume_tac: thm_tactic
val conj_pair: thm.thm -> (thm.thm * thm.thm)
val conjuncts_then: thm_tactic -> thm_tactic
val STRIP_ASSUME_TAC: thm_tactic

val STRIP_ASM_CONJ_TAC: thm_tactic

val x_choose_tac: string -> thm_tactic 

val first_assum: thm_tactic -> tactic
val first_x_assum: thm_tactic -> tactic
val last_assum: thm_tactic -> tactic
val last_x_assum: thm_tactic -> tactic

val conv_canon: thm.thm -> thm.thm list
val fconv_canon: thm.thm -> thm.thm list

val cases_on: form.form -> tactic
val specl_then: term.term list -> thm_tactic -> thm_tactic
end

