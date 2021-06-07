signature tactic = 
sig
type tactic = abbrev.tactic
type thm_tactic = abbrev.thm_tactic
val accept_tac: thm_tactic
val assume_tac: thm_tactic
val conj_tac: tactic
val disj1_tac: tactic
val disj2_tac: tactic
val contra_tac: tactic
val imp_tac: tactic
val dimp_tac: tactic
val wexists_tac: term -> tactic
val gen_tac: tactic
val then_tac: (tactic * tactic) -> tactic
val >> : (tactic * tactic) -> tactic
val then1_tac: (tactic * tactic) -> tactic
val >-- : (tactic * tactic) -> tactic
val Orelse: (tactic * tactic) -> tactic
val stp_tac: tactic
val all_tac: tactic
val repeat: tactic -> tactic 
val assum_list: (thm.thm list -> tactic) -> tactic
val mp_tac: thm_tactic
val rw_tac: thm.thm list -> tactic
val T_INTRO_TAC: tactic
val drule: thm_tactic
end

