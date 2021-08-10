structure proofmanager = 
struct
open goalstack

val current_goal = ref (NONE:gstk option)

fun g0 f = current_goal:= SOME (form_goal (readfq f))


fun PPgstk' gstk =  let val s = ppgstk gstk
                        val SOME (pretty,_,_) = lower s ()
                    in pretty
                    end

fun pgoal action x = (action x; 
                    case !current_goal of 
                        NONE => print "no goal\n"
                      | SOME gstk => print (PP.pp_to_string 75 PPgstk' gstk))

fun g f = pgoal g0 f 


(*M-h g*)

fun e00 tac  = case !current_goal of 
                  NONE => print "no goal \n"
                | SOME gstk => current_goal := SOME (goalstack.e0 tac gstk)

val e = pgoal e00



exception NO_PROOFS;

open History

datatype proof = GOALSTACK of goalstack.gstk history
datatype proofs = PRFS of proof list;

fun initial_proofs() = PRFS[];

fun current_proof (PRFS (p::_)) = p
  | current_proof (PRFS []) = raise NO_PROOFS;



fun new_history_default obj = new_history{obj=obj, limit=15}
(*
fun new_goalstack g f = GOALSTACK(new_history_default (new_goal g f));


fun set_goal g = new_goalstack g Lib.I;  (* historical *)

*)

fun backup (GOALSTACK s) = GOALSTACK(undo s)


fun set_backup i (GOALSTACK s) = GOALSTACK(set_limit s i)

fun restart (GOALSTACK s) = GOALSTACK (new_history_default (initialValue s))




(*fun backup (GOALSTACK s) = GOALSTACK(undo s)*)

fun hd_opr f (PRFS (p::t)) = PRFS(f p::t)
  | hd_opr f otherwise = raise NO_PROOFS;

val the_proofs = ref (initial_proofs());

fun proofs() = !the_proofs;
fun top_proof() = current_proof(proofs());

fun backup' () =
   (the_proofs := hd_opr backup (proofs());
    top_proof());

val b = backup';


fun restore (GOALSTACK s) = GOALSTACK(History.restore s)

fun restore' () =
   (the_proofs := hd_opr restore (proofs());
    top_proof());



fun restart'() =
   (the_proofs := hd_opr restart (proofs());
    top_proof());

end

structure proofManagerLib = struct 
open proofmanager


fun restart() =
   (the_proofs := hd_opr proofmanager.restart (proofs());
    top_proof());

end
