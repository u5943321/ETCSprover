structure form :> form = 
struct
open term
(*datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * sort * (string * sort) list
    | Bound of int
    | Fun of string * sort * term list;
*)
datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;   

val TRUE = Pred("T",[])
val FALSE = Pred("F",[])


exception ERR of string 


fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
      | _ => raise ERR "not an equality"

fun dest_iff f = 
    case f of
        Conn("<=>",[f1,f2]) => (f1,f2)
      | _ => raise ERR "not an iff"

fun is_eqn f = 
    case f of Pred("=",[t1,t2]) => true
            | _ => false


fun eq_form fp = 
    case fp of 
        (Pred(P1,tl1),Pred(P2,tl2)) => 
        P1 = P2 andalso tl1 = tl2
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso s1 = s2 andalso eq_form (b1,b2)
      | _ => false
fun substt (V as (m,s),t2) t = 
    case t of
        Var(n,s') => if m = n andalso s = s' then t2 else t
      | Fun(f,s',tl) => Fun(f,substs (V,t2) s',List.map (substt (V,t2)) tl)
      | _ => t
and substs (V,t2) s = 
    case s of 
        ob => s
      | ar(d,c) => ar(substt (V,t2) d,substt (V,t2) c)


fun substf (V,t2) f = 
    case f of 
        Pred(P,tl) => Pred(P,List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) f)


fun fvt t = 
    case t of 
        Var(n,s) => (n,s) :: (fvs s)
      | Bound i => []
      | Fun(f,s,tl) => 
        (case tl of [] => []
                  | h :: t => (fvt h) @ (fvs s) @ fvt (Fun(f,s,tl)))
and fvs s = 
    case s of 
        ob => []
      | ar(t1,t2) => (fvt t1) @ (fvt t2)

fun fvtl tl = 
    case tl of 
        [] => []
      | h :: t => (fvt h) @ (fvtl t)

fun fvf f = 
    case f of 
        Pred(P,tl) => fvtl tl
      | Conn(co,fl) => 
        (case fl of 
            [] => []
          | h :: t => (fvf h) @ (fvf (Conn(co,t))))
      | Quant(q,n,s,b) => (fvs s) @ (fvf f)

fun fvfl G = 
    case G of [] => []
            | h :: t => (fvf h) @ (fvfl t)

fun replacet (u,new) t = 
    if t=u then new else 
    case t of Fun(f,s,tl) => Fun(f,replaces (u,new) s, map (replacet(u,new)) tl) 
            | _=> t
and replaces (u,new) s = 
    case s of 
        ob => ob
      | ar(t1,t2) => ar(replacet (u,new) t1, replacet  (u,new) t2)

fun abstract t = 
    let fun abs i (Pred(a,ts)) = Pred(a, map (substt (t, Bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, Bound (i + 1)) s, abs (i+1) A)
    in abs 0 end;


fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = Pred(a, List.map (replacet (Bound i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) = Quant(q, n, replaces (Bound (i + 1),t) s, subst (i+1) b)
    in subst 0 end



fun lookup_t env n = Binarymap.peek(env,n)



fun match_term0 pat ct env = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then raise ERR "different function names"
        else match_sort0 s1 s2 (match_tl l1 l2 env)  
      | (Var(n1,s1),_) => 
        (case (lookup_t env n1) of
            SOME t => if t = ct then env else
                      raise ERR "double bind"
          | _ => 
            Binarymap.insert (match_sort0 s1 (sort_of ct) env,n1,ct))
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            raise ERR "bounded variable cannot be unified"
        else env
      | _ => raise Fail "unexpected term constructor"
and match_sort0 sp cs env = 
    case (sp,cs) of 
        (ob,ob) => env
      | (ar(d1,c1),ar(d2,c2)) => 
        match_term0 c1 c2 (match_term0 d1 d2 env)
      | _ => raise ERR "cannot match ob with ar"
and match_tl l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl t1 t2 (match_term0 h1 h2 env)
      | _ => raise ERR "incorrect length of list"


fun match_form pat cf env = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then raise ERR "different predicates"
        else match_tl l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then raise ERR "different connectives"
        else match_fl l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then raise ERR "different quantifiers"
        else match_form b1 b2 (match_sort0 s1 s2 env)
      | _ => raise ERR "different formula constructors"
and match_fl l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl t1 t2 (match_form h1 h2 env)
      | _ => raise ERR "incorrect length of list"

fun inst_term env t = 
    case t of
        Var(n,s) => 
        (case (lookup_t env n) of  
            SOME tm => tm
          | _ => t)
      | Fun(f,s,l) => 
        Fun(f,inst_sort env s,List.map (inst_term env) l)
      | _ => t
and inst_sort env s = 
    case s of 
        ob => ob
      | ar(d,c) => ar(inst_term env d,inst_term env c)

fun inst_form env f = 
    case f of
        Pred(P,tl) => Pred(P,List.map (inst_term env) tl)
      | Conn(co,l) => Conn(co,List.map (inst_form env) l)
      | Quant(q,n,s,b) =>
        Quant(q,n,inst_sort env s, inst_form env b) 

fun strip_all f = 
    case f of 
        Quant("ALL",n,s,b) => strip_all (subst_bound (Var(n,s)) b)
      | _ => f
(*very naive, trying to do the spec stuff*)



end
