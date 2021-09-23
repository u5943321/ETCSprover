structure goalstack :> goalstack = 
struct
open term form logic abbrev tactic parser smpp pp


fun prove f tac = 
    let
        val (subgoals,vfn) = tac (fvf f,[],f)
    in
        case (subgoals) of 
            [] => vfn []
          | h :: t => raise simple_fail "remaining subgoals"
    end

type tac_result = {goals      : goal list,
                   validation : thm list -> thm}

datatype proposition = POSED of goal
                     | PROVED of thm * goal;

datatype gstk = GSTK of {prop  : proposition,
                         stack : tac_result list}

fun new_goal g = GSTK{prop=POSED g, stack=[]}

fun form_goal f = new_goal (fvf f,[]:form list,f)

(*read goal with pretty name*)

fun rapg f = 
    let val f0 = rapf f in new_goal (fvf f0,[]:form list,f0) end

fun proved_th (GSTK{prop:proposition,...}) = 
    case prop of
        PROVED (th,_) => th
      | _ => raise simple_fail "goal is not proved yet"

fun current_tac_result (GSTK{prop,stack:tac_result list}) = 
    case stack of
        [] => raise simple_fail "no remaining goal"
      | h :: t => h

fun current_goal ({goals:goal list,validation:validation}:tac_result) = hd goals
(*

fun current_goal ({goals: goal list,validation : thm list -> thm}:tac_result) = 
    case goals of 
        [] => simple_fail "no goal remains"
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
         | otherwise => raise simple_fail ""
    end
  | return gstk = gstk

fun say s = Lib.say s

fun add_string_cr s = say (s^"\n")
fun cr_add_string_cr s = say ("\n"^s^"\n")
fun imp_err s =
    raise simple_fail ("expandf or expand_listf" ^ "implementation error: "^s)

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
  | expand_msg _ _ = raise simple_fail "3" ;

fun expandf _ (GSTK{prop=PROVED _, ...}) =
    raise simple_fail "expandf: goal has already been proved"
  | expandf tac (GSTK{prop as POSED g, stack}) =
     let val arg = (case stack of [] => g | tr::_ => hd (#goals tr))
         val (glist,vf) = tac arg
         val dpth = length stack
         val gs = return(GSTK{prop=prop,
                              stack={goals=glist, validation=vf} :: stack})
     in expand_msg dpth gs ; gs end

 
fun e0 tac = expandf (valid tac) 


fun ppintf (n,f) = add_string (int_to_string n) >> add_string"." >> 
                              block HOLPP.CONSISTENT 10 (ppform false (LR (NONE,NONE)) f)

fun n2l n = 
    if n > 0 then n :: (n2l (n - 1)) else [] 

fun ppobl l = 
    case l of [] => add_string ""
             | h ::t => add_string h >> add_break (1,0) >> add_string "," >> 
                                   add_break (1,0) >>  ppobl t

fun ppcont c = 
    let val (obs,ars) = partition (fn (n,s) => eq_sort(s,mk_ob_sort)) (HOLset.listItems c)
        val Gvl = List.map (uncurry mk_var) ars
    in block HOLPP.CONSISTENT 10 (ppobl (List.map fst obs) >> add_break (2,0)) >> 
       add_newline >> 
       block HOLPP.CONSISTENT 10
       (pr_list (ppterm true (LR (NONE,NONE))) 
                (add_string "," >> add_break (1,0)) Gvl) 
    end

fun ppgoal (G,A,C) = 
    let
        val Gvl = List.map (uncurry mk_var) (HOLset.listItems G)
    in
        ppcont G >> add_newline >>
               (pr_list ppintf (add_break (1,0)) (rev(zip (n2l (List.length A)) A))) >>
                add_newline >>
                add_string "----------------------------------------------------------------------" >>
                add_newline >>
                block HOLPP.CONSISTENT 10
                (ppform false (LR (NONE,NONE)) C)
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

val cg = current_goal o current_tac_result

end
