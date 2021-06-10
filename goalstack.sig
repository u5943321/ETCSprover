signature goalstack =
sig
    type tac_result 
    datatype proposition = POSED of abbrev.goal
                       | PROVED of thm.thm * abbrev.goal
    datatype gstk = GSTK of {prop  : proposition,
                             stack : tac_result list}
    val prove: form.form -> tactic.tactic -> thm.thm
    val new_goal: abbrev.cont * form.form list * form.form -> gstk
    val read_goal: string -> gstk
    val rpg: string -> gstk
    val rapg: string -> gstk
    val proved_th: gstk -> thm.thm
    val expandf: tactic.tactic -> gstk -> gstk
    val ppgstk: gstk -> ('a, unit) t
    val e: tactic.tactic -> gstk -> gstk
end
