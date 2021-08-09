structure q :> q = 
struct
open pterm tactic

fun q_ttac ttac str: tactic =
    fn (ct,asl,w) => ttac (pwct ct str) (ct,asl,w)

fun q_ftac ftac str: tactic =
    fn (ct,asl,w) => ftac (pwcf ct str) (ct,asl,w)

fun q_tltcl (tltcl:term list -> thm_tactic -> thm_tactic) strl thtac th :tactic = 
    fn (ct,asl,w) => tltcl (List.map (pwct ct) strl) thtac th (ct,asl,w)

val qexists_tac = q_ttac exists_tac

val qspecl_then = q_tltcl specl_then

val qsuff_tac = q_ftac suffices_tac


val qby_tac = q_ftac by_tac


(*what to do pick_assum... val it = fn: form -> thm_tactic -> tactic?
what is the technique of qpat_x_assum? possible to make it more flexible and allow functions as input?

can just do...
*)

fun qpick_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_assum (pwcf ct fstr) thtac (ct,asl,w) 

fun qpick_x_assum fstr (thtac:thm_tactic): tactic = 
    fn (ct,asl,w) => pick_x_assum (pwcf ct fstr) thtac (ct,asl,w) 


end
