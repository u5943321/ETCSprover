structure goalstack :> goalstack = 
struct
open abbrev pterm smpp

fun prove f tac = 
    let
        val (subgoals,vfn) = tac (fvf f,[],f)
    in
        case (subgoals) of 
            [] => vfn []
          | h :: t => raise ERR "remaining subgoals"
    end

type tac_result = {goals      : goal list,
                   validation : thm list -> thm}

datatype proposition = POSED of goal
                     | PROVED of thm * goal;

datatype gstk = GSTK of {prop  : proposition,
                         stack : tac_result list}

fun new_goal (g as (G:(string*sort) set,asl:form list,w:form)) = GSTK{prop=POSED g, stack=[]}

fun read_goal f = 
    let val f0 = readf f in new_goal (fvf f0,[]:form list,f0) end

(*read goal with pretty name*)
fun rpg f = 
    let val f0 = rpf f in new_goal (fvf f0,[]:form list,f0) end

fun proved_th (GSTK{prop:proposition,...}) = 
    case prop of
        PROVED (th,_) => th
      | _ => raise ERR "goal is not proved yet"



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

fun ppgoal (G,A,C) = 
    let
        val Gvl = List.map Var (HOLset.listItems G)
    in
        pr_list (ppterm true (LR (NONE,NONE))) (add_string "," >> add_break (1,0)) Gvl >> add_newline >>
                block HOLPP.INCONSISTENT 2 
                (pr_list (ppform false) (add_string "," >> add_break (1,0)) A) >>
                add_newline >>
                add_string "----------------------------------------------------------------------" >>
                add_newline >>
                block HOLPP.INCONSISTENT 2 
                (ppform false C)
    end 

fun PPgoal printdepth _ th = let val s = ppgoal th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end
fun ppprop prop = 
    case prop of 
        POSED g => ppgoal g
      | PROVED (th,g) => add_string "PROVED!" >> ppthm th 


fun PPprop printdepth _ th = let val s = ppprop th
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPprop

fun ppgoals goals = 
    case goals of [] => add_string ""
                | h :: t => (ppgoal h) >> add_newline >> (ppgoals t)

fun pptac_result ({goals:goal list,validation:thm list -> thm}) = ppgoals goals
    

fun PPtac_result printdepth _ rst = let val s =  pptac_result rst
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end


fun pptac_results trs =
    case trs of [] => add_string ""
              | h :: t => pptac_result h >> add_newline >> pptac_results t

fun ppgstk (GSTK{prop:proposition, stack: tac_result list}) = 
    ppprop prop >> add_newline >> pptac_results stack

fun PPgstk printdepth _ (gstk:gstk) = let val s = ppgstk gstk
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

val _ = PolyML.addPrettyPrinter PPgstk

end
