structure form :> form = 
struct
open term 

(*TODO: edit all the ERR so it outputs the term/form as well*)



datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form
| fVar of string;   

exception ERR of string * sort list * term list * form list 

fun simple_fail s = raise ERR (s,[],[],[]) 

fun replacet (u,new) t = 
    if t=u then new else 
    case t 
     of Fun(f,s,tl) => 
        Fun(f,replaces (u,new) s, List.map (replacet(u,new)) tl) 
      | _=> t
and replaces (u,new) s = 
    case s of 
        ob => ob
      | ar(t1,t2) => ar(replacet (u,new) t1, replacet  (u,new) t2)

fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = Pred(a, List.map (replacet (Bound i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (Bound (i + 1),t) s, subst (i+1) b)
          | subst i (fVar fm) = fVar fm 
    in subst 0 end


fun substt (V as (m,s),t2) t = 
    case t of
        Var(n,s') => 
        if m = n andalso s = s' then t2 
        else Var(n,substs (V,t2) s')
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
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)
      | _ => f

fun abstract t = 
    let fun abs i (Pred(a,ts)) = Pred(a, List.map (substt (t, Bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, Bound (i + 1)) s, abs (i+1) A)
          | abs i (fVar fm) = fVar fm 
    in abs 0 end;



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
      | _ => simple_fail "bad formula"


(*predicate functions*)

fun is_dimp f = 
    case f of
        Conn("<=>",[f1,f2]) => true
      | _ => false

fun is_conj f = 
    case f of
        Conn("&",[f1,f2]) => true
      | _ => false

fun is_neg f = 
    case f of
        Conn("~",[f0]) => true
      | _ => false


fun is_eqn f = 
    case f of Pred("=",[t1,t2]) => true
            | _ => false

fun is_all f = 
    case f of 
        Quant("ALL",_,_,_) => true
      | _ => false


val TRUE = Pred("T",[])

val FALSE = Pred("F",[])

fun mk_neg f = Conn("~",[f])

fun mk_conj f1 f2 = Conn("&",[f1,f2])

fun mk_disj f1 f2 = Conn("|",[f1,f2])

fun mk_imp f1 f2 = Conn("==>",[f1,f2])

fun mk_dimp f1 f2 = Conn("<=>",[f1,f2])

fun mk_all n s b = Quant("ALL",n,s,abstract (n,s) b)

fun mk_exists n s b = Quant("EXISTS",n,s,abstract (n,s) b)

(*destructor functions*)


fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not an equality",[],[],[f])

fun dest_imp f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => simple_fail "not an implication"

fun dest_neg f = 
    case f of
        Conn("~",[f0]) => f0
      | _ => simple_fail "not an negation"


fun dest_conj f = 
    case f of
        Conn("&",[f1,f2]) => (f1,f2)
      | _ => simple_fail "not a conjunction"

fun dest_disj f = 
    case f of
        Conn("|",[f1,f2]) => (f1,f2)
      | _ => simple_fail "not a disjunction"
 

fun dest_dimp f = 
    case f of 
        Conn("<=>",[L,R]) => (L,R)
      | _ => simple_fail ((string_of_form f) ^ " is not a double implication")

fun dest_pred f = 
    case f of 
        Pred(p,l) => (p,l)
      | _ => simple_fail ((string_of_form f) ^ " is not a predicate")

fun dest_exists f = 
    case f of 
        Quant("EXISTS",n,s,b) => ((n,s),b)
      | _ => simple_fail "not an existential"

fun dest_all f = 
    case f of 
        Quant("ALL",n,s,b) => ((n,s),b)
      | _ => simple_fail "not a universal"

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

(*compare functions which help produces HOLsets.*)

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

type menv = ((string * sort),term)Binarymap.dict * (string,form)Binarymap.dict

(*matching environment: records where are term variables and formula variables matched to*)

val emptyvd:(string * sort,term)Binarymap.dict = Binarymap.mkDict (pair_compare String.compare sort_compare)

val emptyfvd:(string,form)Binarymap.dict = Binarymap.mkDict String.compare

val mempty : menv = (emptyvd, Binarymap.mkDict String.compare)

fun v2t V t ((vd,fvd):menv):menv = (Binarymap.insert(vd,V,t),fvd)
    
fun fv2f fm f ((vd,fvd):menv):menv =
    (vd,Binarymap.insert(fvd,fm,f))

fun vd_of ((vd,fvd):menv) = vd

fun fvd_of ((vd,fvd):menv) = fvd

fun lookup_t ((vd,fvd):menv) V = Binarymap.peek (vd,V)

fun lookup_f ((vd,fvd):menv) fm = Binarymap.peek (fvd,fm)

fun mk_menv tenv fenv :menv = (tenv,fenv)

fun mk_tenv l = 
    case l of 
        [] => emptyvd
      | ((n,s),t) :: l0 => Binarymap.insert(mk_tenv l0,(n,s),t)

fun mk_fenv l = 
    case l of 
        [] => emptyfvd
      | (n:string,f:form) :: l0 => Binarymap.insert(mk_fenv l0,n,f)

fun mk_inst tl fl = mk_menv (mk_tenv tl) (mk_fenv fl)

fun pmenv (env:menv) = (Binarymap.listItems (vd_of env),Binarymap.listItems (fvd_of env))

(*TODO: change name to be raw_match*)
fun match_term nss pat ct (env:menv) = 
    case (pat,ct) of 
        (Fun(f1,s1,l1),Fun(f2,s2,l2)) => 
        if f1 <> f2 then simple_fail "different function names"
        else match_sort nss s1 s2 (match_tl nss l1 l2 env)  
      | (Var(n1,s1),_) => 
        if HOLset.member(nss,(n1,s1)) then
            if pat = ct then env 
            else simple_fail "current term not alloed to be instantiated"
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if t = ct then env else
                           simple_fail "double bind"
               | _ => 
                 v2t (n1,s1) ct (match_sort nss s1 (sort_of ct) env))
      | (Bound i1,Bound i2) => 
        if i1 <> i2 then 
            simple_fail "bounded variable cannot be unified"
        else env
      | _ => raise Fail "unexpected term constructor"
and match_sort nss sp cs env = 
    case (sp,cs) of 
        (ob,ob) => env
      | (ar(d1,c1),ar(d2,c2)) => 
        match_term nss c1 c2 (match_term nss d1 d2 env)
      | _ => simple_fail "cannot match ob with ar"
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl nss t1 t2 (match_term nss h1 h2 env)
      | _ => simple_fail "incorrect length of list"



fun match_form nss pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then simple_fail "different predicates"
        else match_tl nss l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then simple_fail "different connectives"
        else match_fl nss l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then simple_fail "different quantifiers"
        else match_form nss b1 b2 (match_sort nss s1 s2 env)
      | (fVar fm,_) => 
            (case (lookup_f env fm) of
                 SOME f => if f = cf then env else
                           simple_fail "double bind"
               | _ => fv2f fm cf env)
      | _ => simple_fail "different formula constructors"
and match_fl nss l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss t1 t2 (match_form nss h1 h2 env)
      | _ => simple_fail "incorrect length of list"


fun strip_all f = 
    case f of 
        Quant("ALL",n,s,b) => 
        let val (b1,l) = strip_all (subst_bound (Var(n,s)) b) in
            (b1,(n,s) :: l) end
      | _ => (f,[])
(*
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
*)
fun pvariantt vd t = 
    case t of 
        Var(n,s) => 
        if (*HOLset.member (vd,(n,s)) *)
            mem n (List.map fst (HOLset.listItems vd))
        then Var (n ^ "'",s)
        else Var (n, s)
      | Fun(f,s,l) => Fun(f,s,List.map (pvariantt vd) l)
      | _ => t

fun inst_term (env:menv) t = 
    case t of 
        Var(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => Var(n,inst_sort env s))
      | Fun(f,s,tl) => Fun(f, inst_sort env s, List.map (inst_term env) tl)
      | _ => t
and inst_sort env s = 
    case s of
        ob => s
      | ar(t1,t2) => ar(inst_term env t1,inst_term env t2)

fun name_clash n env = 
    let
        val new_terms = List.map snd (Binarymap.listItems (vd_of env))
        val new_names = mapfilter (fst o dest_var) new_terms
    in 
        List.exists (fn n0 => n0 = n) new_names
    end

fun rename_once_need n env = 
    if name_clash n env = false then n else rename_once_need (n^"'") env

fun inst_form env f = 
    case f of
        Pred(P,tl) => Pred(P,List.map (inst_term env) tl)
      | Conn(co,fl) => Conn(co,List.map (inst_form env) fl)
      | Quant(q,n,s,b) => 
        let 
            val s' = inst_sort env s
            val b' = inst_form env b
            val n' = rename_once_need n env 
        in 
            Quant(q,n',s',b')
        end
      | fVar fvn => 
        (case lookup_f env fvn of
             SOME f' => f'
           | NONE => f)


fun psymsf f = 
    case f of 
        Pred(p,_) => HOLset.add(HOLset.empty String.compare,p)
      | Conn("~",[A]) => psymsf A
      | Conn(_,[A,B]) => HOLset.union(psymsf A,psymsf B)
      | Quant(_,_,_,b) => psymsf b
      | _ => simple_fail 
                   ("formula: " ^ (string_of_form f) ^ " is not well-formed")

fun fsymss s = 
    case s of
        ob => HOLset.empty String.compare
      | ar(d,c) => HOLset.union(fsymst d,fsymst c)
and fsymst t = 
    case t of
        Var(n,s) => fsymss s
      | Fun(_,s,l) => 
        let val argfs = List.foldr 
                            (fn (t,fs) => HOLset.union (fsymst t,fs))
                            (HOLset.empty String.compare)
                            l
        in HOLset.union(argfs,fsymss s)
        end
      | _ => HOLset.empty String.compare

fun fsymsf f = 
    case f of 
        Pred(_,l) => 
        List.foldr 
            (fn (t,fs) => HOLset.union (fsymst t,fs))
            (HOLset.empty String.compare)
            l
      | Conn("~",[A]) => fsymsf A
      | Conn(_,[A,B]) => HOLset.union(fsymsf A,fsymsf B)
      | Quant(_,_,_,b) => fsymsf b
      | _ => simple_fail 
                   ("formula: " ^ (string_of_form f) ^ " is not well-formed")



fun is_ss_ob (n:string,s) = if s = ob then true else false

(*dpcy for dependency*)

fun ok_dpdc (env:menv) ((n:string,s),t) = 
    if sort_of t = inst_sort env s then true else false
    

fun is_wfmenv menv = 
    let val pairs = Binarymap.listItems (vd_of menv)
    in List.all (ok_dpdc menv) pairs
    end

end
