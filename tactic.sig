signature tactic = 
sig
type form = form.form
type term = term.term
type thm = thm.thm
type goal = form list * form
type validation = thm list -> thm
type tactic = goal -> goal list * validation
val conj_tac: tactic
val disj1_tac: tactic
val disj2_tac: tactic
val contra_tac: tactic
val imp_tac: tactic
val dimp_tac: tactic
val wexists_tac: term -> tactic
val then_tac: (tactic * tactic) -> tactic
val then1_tac: (tactic * tactic) -> tactic
val Orelse: (tactic * tactic) -> tactic
val stp_tac: tactic
val all_tac: tactic
val repeat: tactic -> tactic 
end

