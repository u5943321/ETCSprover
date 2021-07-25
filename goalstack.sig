signature goalstack =
sig
    include abbrev
    type tac_result 
    datatype proposition = POSED of abbrev.goal
                       | PROVED of logic.thm * abbrev.goal
    datatype gstk = GSTK of {prop  : proposition,
                             stack : tac_result list}
    val prove: form.form -> tactic.tactic -> logic.thm
    val new_goal: abbrev.cont * form.form list * form.form -> gstk
    val read_goal: string -> gstk
    val rpg: string -> gstk
    val rapg: string -> gstk
    val proved_th: gstk -> logic.thm
    val ppgstk: gstk -> ('a, unit) smpp.t
    val expandf: tactic.tactic -> gstk -> gstk
    val e0: tactic.tactic -> gstk -> gstk
    val current_goal: tac_result -> abbrev.goal
    val current_tac_result: gstk -> tac_result
    val cg: gstk -> abbrev.goal
end
