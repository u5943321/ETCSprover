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
| Quant of string * string * sort * form
| fVar of string;   

val TRUE = Pred("T",[])
val FALSE = Pred("F",[])

fun mk_ob a = Var(a,ob)
fun mk_ar a A B = Var(a,ar(mk_ob A,mk_ob B))

fun mk_neg f = Conn("~",[f])

fun mk_conj f1 f2 = Conn("&",[f1,f2])

fun mk_disj f1 f2 = Conn("|",[f1,f2])

fun mk_imp f1 f2 = Conn("==>",[f1,f2])

fun mk_dimp f1 f2 = Conn("<=>",[f1,f2])


exception ERR of string 

(*destructor functions*)

fun dest_fun t = 
    case t of
        Fun(f,s,l) => (f,s,l)
      | _ => raise ERR "not a function term"

fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
      | _ => raise ERR "not an equality"

fun dest_iff f = 
    case f of
        Conn("<=>",[f1,f2]) => (f1,f2)
      | _ => raise ERR "not an iff"

fun dest_imp f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR "not an implication"

fun dest_conj f = 
    case f of
        Conn("&",[f1,f2]) => (f1,f2)
      | _ => raise ERR "not a conjunction"

(*predicate functions*)

fun is_eqn f = 
    case f of Pred("=",[t1,t2]) => true
            | _ => false

fun is_all f = 
    case f of 
        Quant("ALL",_,_,_) => true
      | _ => false


fun eq_form fp = 
    case fp of 
        (Pred(P1,tl1),Pred(P2,tl2)) => 
        P1 = P2 andalso tl1 = tl2
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso s1 = s2 andalso eq_form (b1,b2)
      | (fVar fm1,fVar fm2)  => fm1 = fm2
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
      | _ => f

fun pair_compare ac bc ((a1,b1),(a2,b2)) = 
    case (ac (a1,a2)) of 
        EQUAL => bc (b1,b2)
      | x => x


fun inv_image_compare f c (x,y) = 
    c (f x, f y)

fun list_compare c (l1,l2) = 
    case (l1,l2) of
        ([],[]) => EQUAL
      | (h1 :: t1, h2 :: t2) => pair_compare c (list_compare c)
                                             ((h1,t1),(h2,t2))
      | ([],_) => LESS
      | (_,[]) => GREATER

fun sort_compare (s1,s2) = 
    case (s1,s2) of 
        (ob,ob) => EQUAL
      | (ob,_) => LESS
      | (_,ob) => GREATER
      | (ar dc1,ar dc2) => pair_compare term_compare term_compare (dc1,dc2)
and term_compare (t1,t2) = 
    case (t1,t2) of 
        (Var ns1,Var ns2) => pair_compare String.compare sort_compare (ns1,ns2)
     | (Var _ , _) => LESS
     | (_,Var _) => GREATER
     | (Bound i1, Bound i2) => Int.compare (i1,i2)
     | (Bound _ , _) => LESS
     | (_, Bound _) => GREATER
     | (Fun fsl1, Fun fsl2) => 
       inv_image_compare (fn (a,b,c) => (a,(b,c))) 
                         (pair_compare String.compare 
                                       (pair_compare sort_compare 
                                                     (list_compare term_compare))) 
                         (fsl1,fsl2)  

(*empty string-sort-pair set*)
val essps = 
    HOLset.empty (pair_compare String.compare sort_compare)

fun fvt t = 
    case t of 
        Var(n,s) => HOLset.add (fvs s,(n,s)) 
      | Bound i => essps
      | Fun(f,s,tl) => 
        (case tl of 
             [] => essps
           | h :: t => HOLset.union 
                           (HOLset.union ((fvt h),(fvs s)), 
                            fvtl t))
and fvs s = 
    case s of 
        ob => essps
      | ar(t1,t2) => HOLset.union (fvt t1,fvt t2)
and fvtl tl = 
    case tl of 
        [] => essps
      | h :: t => HOLset.union (fvt h,fvtl t)


fun fvf f = 
    case f of 
        Pred(P,tl) => fvtl tl
      | Conn(co,fl) => fvfl fl
      | Quant(q,n,s,b) => HOLset.union (fvs s,fvf b)
      | _ => essps
and fvfl G = 
    case G of [] => essps
            | h :: t => HOLset.union (fvf h,fvfl t)

fun replacet (u,new) t = 
    if t=u then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (u,new) s, map (replacet(u,new)) tl) 
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
          | abs i (fVar fm) = fVar fm 
    in abs 0 end;

fun mk_all n s b = Quant("ALL",n,s,abstract (n,s) b)

fun mk_exists n s b = Quant("EXISTS",n,s,abstract (n,s) b)

fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = Pred(a, List.map (replacet (Bound i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (Bound (i + 1),t) s, subst (i+1) b)
          | subst i (fVar fm) = fVar fm 
    in subst 0 end



fun lookup_t env n = Binarymap.peek(env,n)



fun match_term pat ct env = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then raise ERR "different function names"
        else match_sort s1 s2 (match_tl l1 l2 env)  
      | (Var(n1,s1),_) => 
        (case (lookup_t env (n1,s1)) of
            SOME t => if t = ct then env else
                      raise ERR "double bind"
          | _ => 
            Binarymap.insert 
                (match_sort s1 (sort_of ct) env,(n1,s1),ct))
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            raise ERR "bounded variable cannot be unified"
        else env
      | _ => raise Fail "unexpected term constructor"
and match_sort sp cs env = 
    case (sp,cs) of 
        (ob,ob) => env
      | (ar(d1,c1),ar(d2,c2)) => 
        match_term c1 c2 (match_term d1 d2 env)
      | _ => raise ERR "cannot match ob with ar"
and match_tl l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl t1 t2 (match_term h1 h2 env)
      | _ => raise ERR "incorrect length of list"


type menv = ((string * sort),term)Binarymap.dict * (string,form)Binarymap.dict

val emptyvd = Binarymap.mkDict (pair_compare String.compare sort_compare)

val mempty : menv = (emptyvd, Binarymap.mkDict String.compare)

fun v2t V t ((vd,fvd):menv):menv = (Binarymap.insert(vd,V,t),fvd)
    
fun fv2f fm f ((vd,fvd):menv):menv =
    (vd,Binarymap.insert(fvd,fm,f))

fun vd_of ((vd,fvd):menv) = vd

fun fvd_of ((vd,fvd):menv) = fvd

fun lookup_t ((vd,fvd):menv) V = Binarymap.peek (vd,V)

fun lookup_f ((vd,fvd):menv) fm = Binarymap.peek (fvd,fm)

fun mk_menv tenv fenv :menv = (tenv,fenv)


fun match_term pat ct (env:menv) = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then raise ERR "different function names"
        else match_sort s1 s2 (match_tl l1 l2 env)  
      | (Var(n1,s1),_) => 
        (case (lookup_t env (n1,s1)) of
            SOME t => if t = ct then env else
                      raise ERR "double bind"
          | _ => 
            v2t (n1,s1) ct (match_sort s1 (sort_of ct) env))
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            raise ERR "bounded variable cannot be unified"
        else env
      | _ => raise Fail "unexpected term constructor"
and match_sort sp cs env = 
    case (sp,cs) of 
        (ob,ob) => env
      | (ar(d1,c1),ar(d2,c2)) => 
        match_term c1 c2 (match_term d1 d2 env)
      | _ => raise ERR "cannot match ob with ar"
and match_tl l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl t1 t2 (match_term h1 h2 env)
      | _ => raise ERR "incorrect length of list"



fun match_form pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then raise ERR "different predicates"
        else match_tl l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then raise ERR "different connectives"
        else match_fl l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then raise ERR "different quantifiers"
        else match_form b1 b2 (match_sort s1 s2 env)
      | (fVar fm,_) => fv2f fm cf env
      | _ => raise ERR "different formula constructors"
and match_fl l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl t1 t2 (match_form h1 h2 env)
      | _ => raise ERR "incorrect length of list"

(*
fun inst_term env t = 
    case t of
        Var(n,s) => 
        (case (lookup_t env (n,s)) of  
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
*)

fun strip_all f = 
    case f of 
        Quant("ALL",n,s,b) => strip_all (subst_bound (Var(n,s)) b)
      | _ => f
(*very naive, trying to do the spec stuff*)




fun strip_ALL f = 
    let fun strip_all0 f = 
            case f of 
                Quant("ALL",n,s,b) => 
                let val (b1,l) = strip_all0 (subst_bound (Var(n,s)) b) in
                    (b1,(n,s) :: l) end
              | _ => (f,[])
    in strip_all0 f
    end


fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if HOLset.member (vd,(n,s))
        then Var (n ^ "'",pvariants vd s)
        else Var (n, pvariants vd s)
      | Fun(f,s,l) => Fun(f,pvariants vd s,List.map (pvariantt vd) l)
      | _ => t
and pvariants vl s = 
    case s of  
        ob => ob
      | ar(t1,t2) => ar(pvariantt vl t1,pvariantt vl t2)

(*
fun fVarinf f = 
    case f of
        Pred _ => 
        HOLset.empty (pair_compare String.compare sort_compare)
      | Conn(co,[f1,f2]) => 
        HOLset.union (fVarinf f1,fVarinf f2)
      | Conn(co,[f0]) => fVarinf f0
      | Quant(_,_,_,b) => fVarinf b
      | _ => raise ERR "ill-formed formula"
*)

fun fVarinf f = 
    case f of
        Pred _ => []
      | Conn(co,[f1,f2]) => (fVarinf f1) @ (fVarinf f2)
      | Conn(co,[f0]) => fVarinf f0
      | Quant(_,_,_,b) => fVarinf b
      | fVar fm => [fm]
      | _ => raise ERR "ill-formed formula"

fun inst_fVar (fm,f0) f = 
    case f of 
        Pred(_,_) => f
      | Conn(co,fl) => Conn(co,List.map (inst_fVar (fm,f0)) fl)
      | Quant(q,n,s,b) =>
        let val n0 = 
                if mem n (fVarinf f0) then n ^ "'" else n
        in Quant(q,n ^ "'",s,inst_fVar (fm,f0) b)
        end
      | fVar ff => if ff = fm then f0 else f

fun inst_fVarl l f = 
    case l of 
        [] => f
      | (nh,fh) :: t =>
        inst_fVar (nh,fh) (inst_fVarl t f)

fun inst_fVare (env:menv) f = 
    let val fVs = Binarymap.listItems (fvd_of env)
    in inst_fVarl fVs f
    end

fun enclose a = "(" ^ a ^ ")";

fun conc_list sep l = 
    case l of 
        [] => ""
      | h :: t => sep ^ h ^ conc_list sep t

fun conc_list1 sep l = 
    case l of [] => ""
            | h :: t => h  ^ (conc_list sep t);


(* with sorts
fun string_of_tl l = 
    case l of
        [] => ""
      | h :: t => 
        enclose (conc_list1 ","
                            (List.map string_of_term (h :: t)))
and string_of_term t = 
    case t of
        Var(n,s) => n ^ ":" ^ string_of_sort s
      | Fun(f,s,[t1,t2]) => 
        enclose 
            ((string_of_term t1) ^ " " ^ f ^ " " ^ 
             (string_of_term t2)) ^ 
        ":" ^ string_of_sort s
      | Fun(f,s,l) => 
        f ^ (string_of_tl l) ^ ":" ^ string_of_sort s
      | _ => " "
and string_of_sort s = 
    case s of 
        ob => "ob"
      | ar(A,B) => (string_of_term A) ^ "-->" ^ (string_of_term B)
*)

fun string_of_tl l = 
    case l of
        [] => ""
      | h :: t => 
        enclose (conc_list1 ","
                            (List.map string_of_term (h :: t)))
and string_of_term t = 
    case t of
        Var(n,s) => n
      | Fun(f,s,[t1,t2]) => 
        enclose 
            ((string_of_term t1) ^ " " ^ f ^ " " ^ 
             (string_of_term t2)) 
      | Fun(f,s,l) => 
        f ^ (string_of_tl l)
      | _ => ""
and string_of_sort s = 
    case s of 
        ob => "ob"
      | ar(A,B) => (string_of_term A) ^ "-->" ^ (string_of_term B)



fun string_of_form f = 
    case f of
        Pred(p,[t1,t2]) => 
        (string_of_term t1) ^ " " ^ p ^ " " ^ (string_of_term t2)
      | Pred(p,tl) =>  p ^ string_of_tl tl
      | Conn(co,[f1,f2]) =>
        string_of_form f1 ^ co ^ string_of_form f2
      | Conn(co,[f]) => co ^ string_of_form f
      | Quant(q,n,s,b) => 
        q ^ string_of_term (Var(n,s)) ^ "." ^
        string_of_form 
            (subst_bound (Var(n,s)) b)
      | fVar fm => "fV" ^ enclose fm
      | _ => raise ERR "bad formula"

(*basic_fconv c basic_taut_fconv (Quant ("ALL", "x", ob, Conn ("|", [Pred ("T", []), Pred ("F", [])])));*)
  

(*Variables To Be Specialized*)


(*
fun part_tmatch pfn th t = 
    let
        val env = match_term0 (pfn th) t (Binarymap.mkDict String.compare)
    in
        (List.map (inst_form env) (ant th), inst_form env (concl th))
    end
*)

end
