structure form :> form = 
struct
open term 

datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form
| fVar of string;   

datatype form_view =
    vConn of string * form list
  | vQ of string * string * sort * form
  | vPred of string * term list
  | vfVar of string

fun view_form f =
    case f of
        Conn sfs => vConn sfs
      | Quant qi => vQ qi
      | Pred pi => vPred pi
      | fVar f => vfVar f

exception ERR of string * sort list * term list * form list 

fun simple_fail s = ERR (s,[],[],[]) 

fun subst_bound t = 
    let fun subst i (Pred(a,ts)) = Pred(a, List.map (replacet (mk_bound i, t)) ts) 
          | subst i (Conn(b,As)) = Conn(b, List.map (subst i) As) 
          | subst i (Quant(q,n,s,b)) =
            Quant(q, n, replaces (mk_bound (i + 1),t) s, subst (i+1) b)
          | subst i (fVar fm) = fVar fm 
    in subst 0 end



fun substf (V,t2) f = 
    case f of 
        Pred(P,tl) => Pred(P,List.map (substt (V,t2)) tl)
      | Conn(co,fl) => Conn(co,List.map (substf (V,t2)) fl)
      | Quant(q,n,s,b) => Quant(q,n,substs (V,t2) s,substf (V,t2) b)
      | _ => f

fun abstract t = 
    let fun abs i (Pred(a,ts)) = Pred(a, List.map (substt (t,mk_bound i)) ts) 
          | abs i (Conn(b,As)) = Conn(b, List.map (abs i) As) 
          | abs i (Quant(q,b,s,A)) = 
            Quant(q, b, substs (t, mk_bound (i + 1)) s, abs (i+1) A)
          | abs i (fVar fm) = fVar fm 
    in abs 0 end;

(*

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
      | _ => raise ERR ("bad formula: ",[],[],[f])
*)

(*predicate functions*)

fun is_imp f = 
    case f of
        Conn("==>",[f1,f2]) => true
      | _ => false

fun is_dimp f = 
    case f of
        Conn("<=>",[f1,f2]) => true
      | _ => false

fun is_conj f = 
    case f of
        Conn("&",[f1,f2]) => true
      | _ => false


fun is_disj f = 
    case f of
        Conn("|",[f1,f2]) => true
      | _ => false

fun is_neg f = 
    case f of
        Conn("~",[f0]) => true
      | _ => false


fun is_eq f = 
    case f of Pred("=",[t1,t2]) => true
            | _ => false

fun is_forall f = 
    case f of 
        Quant("!",_,_,_) => true
      | _ => false


fun is_exists f = 
    case f of 
        Quant("?",_,_,_) => true
      | _ => false


fun is_quant f = 
    case f of 
        Quant _ => true
      | _ => false


val TRUE = Pred("T",[])

val FALSE = Pred("F",[])

fun mk_conn co fl = Conn(co,fl)

fun mk_neg f = Conn("~",[f])

fun mk_conj f1 f2 = Conn("&",[f1,f2])

fun mk_disj f1 f2 = Conn("|",[f1,f2])

fun mk_imp f1 f2 = Conn("==>",[f1,f2])

fun mk_dimp f1 f2 = Conn("<=>",[f1,f2])

fun mk_forall n s b = Quant("!",n,s,abstract (n,s) b)

fun mk_exists n s b = Quant("?",n,s,abstract (n,s) b)

fun mk_quant q n s b = Quant(q,n,s,abstract (n,s) b)

fun mk_P0 p tl = if is_pred p then Pred(p,tl)
                    else raise ERR ("mk_pred.psym: " ^ p ^ " not found",[],tl,[]) 

fun mk_pred p tl = case lookup_pred (!psyms) p of 
                       NONE => raise ERR ("mk_pred.psym not found",[],tl,[]) 
                      | SOME l =>  Pred(p,tl)

fun mk_eq t1 t2 = mk_pred "=" [t1,t2]

fun mk_fvar f = fVar f

(*TODO: check mk_fun as well!! edit it to do a matching!*)
(*destructor functions*)


fun dest_eq f = 
    case f of
        Pred("=",[t1,t2]) => (t1,t2)
      | _ => raise ERR ("not an equality: ",[],[],[f])

fun dest_imp f = 
    case f of 
        Conn("==>",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a implication: ",[],[],[f])

fun dest_neg f = 
    case f of
        Conn("~",[f0]) => f0
      | _ => raise ERR ("not a negation: ",[],[],[f])


fun dest_conj f = 
    case f of
        Conn("&",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a conjunction: ",[],[],[f])

fun dest_disj f = 
    case f of
        Conn("|",[f1,f2]) => (f1,f2)
      | _ => raise ERR ("not a disjunction: ",[],[],[f])
 

fun dest_dimp f = 
    case f of 
        Conn("<=>",[L,R]) => (L,R)
      | _ => raise ERR ("not a double implication: ",[],[],[f])


fun dest_pred f = 
    case f of 
        Pred(p,l) => (p,l)
      | _ => raise ERR ("not a predicate: ",[],[],[f])

fun dest_exists f = 
    case f of 
        Quant("?",n,s,b) => ((n,s),b)
      | _ => raise ERR ("not an existantial: ",[],[],[f])

fun dest_forall f = 
    case f of 
        Quant("!",n,s,b) => ((n,s),b)
      | _ => raise ERR ("not a universal",[],[],[f])


fun eq_form fp = 
    case fp of 
        (Pred(P1,tl1),Pred(P2,tl2)) => 
        P1 = P2 andalso List.all eq_term (zip tl1 tl2)
      | (Conn(co1,fl1),Conn(co2,fl2)) => co1 = co2 andalso 
                                         ListPair.all eq_form (fl1,fl2)
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        q1 = q2 andalso eq_sort(s1,s2) andalso eq_form (b1,b2)
      | (fVar fm1,fVar fm2)  => fm1 = fm2
      | _ => false

fun eq_forml (l1:form list) (l2:form list) = 
    case (l1,l2) of 
        ([],[]) => true
      | (h1 :: t1, h2 :: t2) => eq_form(h1,h2) andalso eq_forml t1 t2
      | _  => raise simple_fail "eq_forml.different length of lists"

fun fmem f fl = List.exists (curry eq_form f) fl

fun ril i l = 
    case l of [] => []
            | h :: t => 
              if eq_form(h,i) then t else h :: (ril i t)

(*compare functions which help produces HOLsets.*)

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

fun mk_fenv l = 
    case l of 
        [] => emptyfvd
      | (n:string,f:form) :: l0 => Binarymap.insert(mk_fenv l0,n,f)

fun mk_inst tl fl = mk_menv (mk_tenv tl) (mk_fenv fl)

fun pmenv (env:menv) = (Binarymap.listItems (vd_of env),Binarymap.listItems (fvd_of env))


fun match_term nss pat ct (env:menv) = 
    case (view_term pat,view_term ct) of 
        (vFun(f1,s1,l1),vFun(f2,s2,l2)) => 
        if f1 <> f2 then 
            raise ERR ("different function names: ",[],[pat,ct],[])
        else match_sort nss s1 s2 (match_tl nss l1 l2 env)  
      | (vVar(n1,s1),_) => 
        if HOLset.member(nss,(n1,s1)) then
            if eq_term(pat,ct) then env 
            else raise ERR ("current term is local constant: ",[],[pat,ct],[])
        else 
            (case (lookup_t env (n1,s1)) of
                 SOME t => if eq_term(t,ct) then env else
                           raise ERR ("double bind: ",[],[pat,t,ct],[])
               | _ => 
                 v2t (n1,s1) ct (match_sort nss s1 (sort_of ct) env))
      | (vB i1,vB i2) => 
        if i1 <> i2 then 
            raise ERR ("bound variables have different levels: ",[],[pat,ct],[])
        else env
      | _ => raise Fail "unexpected term constructor"
and match_sort nss sp cs env = 
    case (view_sort sp,view_sort cs) of 
        (vo,vo) => env
      | (va(d1,c1),va(d2,c2)) => 
        match_term nss c1 c2 (match_term nss d1 d2 env)
      | _ => raise ERR ("cannot match ob with ar: ",[sp,cs],[],[])
and match_tl nss l1 l2 env =
    case (l1,l2) of 
        ([],[]) => env
      | (h1 :: t1,h2 :: t2) => 
        match_tl nss t1 t2 (match_term nss h1 h2 env)
      | _ => raise ERR ("incorrect length of list",[],[],[])



fun match_form nss pat cf env:menv = 
    case (pat,cf) of
        (Pred(P1,l1),Pred(P2,l2)) => 
        if P1 <> P2 then 
            raise ERR ("different predicates: ",[],[],[pat,cf])
        else match_tl nss l1 l2 env
      | (Conn(co1,l1),Conn(co2,l2)) => 
        if co1 <> co2 then 
            raise ERR ("different connectives: ",[],[],[pat,cf])
        else match_fl nss l1 l2 env
      | (Quant(q1,n1,s1,b1),Quant(q2,n2,s2,b2)) => 
        if q1 <> q2 then 
            raise ERR ("different quantifiers: ",[],[],[pat,cf])
        else match_form nss b1 b2 (match_sort nss s1 s2 env)
      | (fVar fm,_) => 
            (case (lookup_f env fm) of
                 SOME f => if eq_form(f,cf) then env else
                           raise ERR ("double bind of formula variables",[],[],[pat,f,cf])
               | _ => fv2f fm cf env)
      | _ => raise ERR ("different formula constructors",[],[],[pat,cf])
and match_fl nss l1 l2 env = 
    case (l1,l2) of 
        ([],[]) => env
      | (h1::t1,h2::t2) =>  
        match_fl nss t1 t2 (match_form nss h1 h2 env)
      | _ => raise simple_fail "incorrect length of list"


fun strip_forall f = 
    case f of 
        Quant("!",n,s,b) => 
        let val (b1,l) = strip_forall (subst_bound (mk_var n s) b) in
            (b1,(n,s) :: l) end
      | _ => (f,[])

fun strip_exists f = 
    case f of 
        Quant("?",n,s,b) => 
        let val (b1,l) = strip_exists (subst_bound (mk_var n s) b) in
            (b1,(n,s) :: l) end
      | _ => (f,[])

fun strip_quants f = 
    case f of 
        Quant(q,_,_,_) => if q = "!" then strip_forall f 
                          else if q = "?" then strip_exists f 
                          else raise ERR ("strip_exists.not a quantified formula",[],[],[f])
      | _ => raise ERR ("strip_exists.not a quantified formula",[],[],[f])



(*TODO: strip_conj strip_disj etc, have it, in iffLR? *)

fun inst_term (env:menv) t = 
    case view_term t of 
        vVar(n,s) => 
        (case lookup_t env (n,s) of 
             SOME t' => t'
           | _ => mk_var n (inst_sort env s))
      | vFun(f,s,tl) => mk_fun f (inst_sort env s) (List.map (inst_term env) tl)
      | _ => t
and inst_sort env s = 
    case view_sort s of
        vo => s
      | va(t1,t2) => mk_ar_sort (inst_term env t1) (inst_term env t2)

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
      | _ => raise ERR ("psymsf.ill-formed formula: ",[],[],[f])

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
      | _ => raise ERR ("fsymfs.ill-formed formula: ",[],[],[f])



fun is_ss_ob (n:string,s) = if eq_sort(s,mk_ob_sort) then true else false
(*TODO: why need this function above?*)


(*dpcy for dependency*)

fun ok_dpdc (env:menv) ((n:string,s),t) = 
    if eq_sort(sort_of t,inst_sort env s) then true else false
    

fun is_wfmenv menv = 
    let val pairs = Binarymap.listItems (vd_of menv)
    in List.all (ok_dpdc menv) pairs
    end

end
