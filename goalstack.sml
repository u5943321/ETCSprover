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

fun rapg f = 
    let val f0 = rapf f in new_goal (fvf f0,[]:form list,f0) end

fun proved_th (GSTK{prop:proposition,...}) = 
    case prop of
        PROVED (th,_) => th
      | _ => raise ERR "goal is not proved yet"

fun current_tac_result (GSTK{prop,stack:tac_result list}) = 
    case stack of
        [] => raise ERR "no remaining goal"
      | h :: t => h

fun current_goal ({goals:goal list,validation:validation}:tac_result) = hd goals
(*

fun current_goal ({goals: goal list,validation : thm list -> thm}:tac_result) = 
    case goals of 
        [] => raise ERR "no goal remains"
      | h :: t => h

*)


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



fun e tac = expandf (valid tac) 
fun e0 tac = expandf (valid tac) 

(*
fun e tac = expandf (VALID tac) 
do valid check on each step.
*)

fun ppintf (n,f) = add_string (int_to_string n) >> add_string"." >> 
                              block HOLPP.CONSISTENT 10 (ppform false f)

fun n2l n = 
    if n > 0 then n :: (n2l (n - 1)) else [] 

fun ppobl l = 
    case l of [] => add_string ""
             | h ::t => add_string h >> add_break (1,0) >> add_string "," >> 
                                   add_break (1,0) >>  ppobl t

fun ppcont c = 
    let val (obs,ars) = partition (fn (n,s) => s = ob) (HOLset.listItems c)
        val Gvl = List.map Var ars
    in block HOLPP.CONSISTENT 10 (ppobl (List.map fst obs) >> add_break (2,0)) >> 
       add_newline >> 
       block HOLPP.CONSISTENT 10
       (pr_list (ppterm true (LR (NONE,NONE))) 
                (add_string "," >> add_break (1,0)) Gvl) 
    end

fun ppgoal (G,A,C) = 
    let
        val Gvl = List.map Var (HOLset.listItems G)
    in
        ppcont G >> add_newline >>
               (pr_list ppintf (add_break (1,0)) (rev(zip (n2l (List.length A)) A))) >>
                add_newline >>
                add_string "----------------------------------------------------------------------" >>
                add_newline >>
                block HOLPP.CONSISTENT 10
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

fun pptac_result ({goals:goal list,validation:thm list -> thm}) = ppgoals (rev goals)
    

fun PPtac_result printdepth _ rst = let val s =  pptac_result rst
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end

(*val _ = PolyML.addPrettyPrinter PPtac_result*)

fun ppgstk (GSTK{prop:proposition, stack: tac_result list}) = 
    case stack of [] => ppprop prop | h :: t => pptac_result h

(*
fun ppgstk (GSTK{prop:proposition, stack = ({goals,...}::_)}) = ppgoals goals
  | ppgstk (GSTK{prop:proposition, stack = []}) = ppprop prop 
*)

fun PPgstk printdepth _ (gstk:gstk) = let val s = ppgstk gstk
                             val SOME (pretty,_,_) = lower s ()
                         in pretty
                         end


(*print out the hd of tac result list, do not print out the prop*)
val _ = PolyML.addPrettyPrinter PPgstk



end
