
type tac_result = {goals      : goal list,
                   validation : thm list -> thm}

datatype proposition = POSED of goal
                     | PROVED of thm * goal;

fun prove f tac = 
    let
        val (subgoals,vfn) = tac ([],f)
    in
        case (subgoals) of 
            [] => vfn []
          | h :: t => raise ERR "remaining subgoals"
    end

datatype gstk = GSTK of {prop  : proposition,
                         stack : tac_result list}

fun return(GSTK{stack={goals=[],validation}::rst, prop as POSED g}) =
    let val th = validation []
    in case rst
        of [] => GSTK{prop=PROVED (th,g), stack=[]}
         | {goals = _::rst_o_goals, validation}::rst' =>
           (
             return(GSTK{prop=prop, 
                         stack={goals=rst_o_goals,
                                validation=fn thl => validation(th::thl)}::rst'})
           )
         | otherwise => raise ERR ""
    end
  | return gstk = gstk

fun say s = Lib.say s

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")
fun imp_err s =
    raise ERR ("expandf or expand_listf" ^ "implementation error: "^s)


fun expand_msg dpth (GSTK{prop = PROVED _, ...}) = ()
  | expand_msg dpth (GSTK{prop, stack as {goals, ...}::_}) =
    let val dpth' = length stack
    in if dpth' > dpth
       then if (dpth+1 = dpth')
            then add_string_cr
                     (case (length goals)
                       of 0 => imp_err "1"
                        | 1 => "1 subgoal:"
                        | n => (int_to_string n)^" subgoals:")
            else imp_err "2"
       else cr_add_string_cr "Remaining subgoals:"
    end
  | expand_msg _ _ = raise ERR "3" ;


fun expandf _ (GSTK{prop=PROVED _, ...}) =
       raise ERR "expandf: goal has already been proved"
  | expandf tac (GSTK{prop as POSED g, stack}) =
     let val arg = (case stack of [] => g | tr::_ => hd (#goals tr))
         val (glist,vf) = tac arg
         val dpth = length stack
         val gs = return(GSTK{prop=prop,
                              stack={goals=glist, validation=vf} :: stack})
     in expand_msg dpth gs ; gs end

