structure proofmanager = 
struct
open goalstack

val current_goal = ref (NONE:gstk option)

fun g0 f = current_goal:= SOME (rpg f)


fun PPgstk' gstk =  let val s = ppgstk gstk
                        val SOME (pretty,_,_) = lower s ()
                    in pretty
                    end

fun pgoal action x = (action x; 
                    case !current_goal of 
                        NONE => print "no goal\n"
                      | SOME gstk => print (PP.pp_to_string 75 PPgstk' gstk))

fun g f = pgoal g0 f 

fun e00 tac  = case !current_goal of 
                  NONE => print "no goal \n"
                | SOME gstk => current_goal := SOME (goalstack.e0 tac gstk)

val e = pgoal e00


end

structure proofManagerLib = proofmanager
open proofmanager 
