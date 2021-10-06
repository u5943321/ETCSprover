structure logic :> logic = 
struct
open term form

datatype thm = thm of ((string * sort) set * form list * form) 
datatype thm_view = vth of ((string * sort) set * form list * form) 

fun view_thm (thm(G,A,C)) = vth (G,A,C)

fun dest_thm (thm(G,A,C)) = (G,A,C)

fun mk_thm G A C = thm(G,A,C)

fun mk_fth f = thm(fvf f,[],f)

fun ant (thm(_,A,_)) = A

fun concl (thm(_,_,C)) = C 

fun cont (thm(G,_,_)) = G

fun eq_thm th1 th2 = 
    HOLset.equal(cont th1,cont th2) andalso
    eq_forml (ant th1) (ant th2) andalso
    eq_form (concl th1, concl th2)

(**********************************************************************

A, Γ |- C
-------------------- inst_thm env
A', Γ' |- C'

A',C' is obtained by pluging in variables recorded in env
Γ' is obtained by collecting all variables in substituted Γ.

**********************************************************************)

fun mk_sss l = List.foldr HOLset.union essps l

fun inst_thm env th = 
    if is_wfmenv env then
        let
            val G0 = HOLset.listItems (cont th)
            val G = mk_sss (List.map (fvt o (inst_term (vd_of env)) o (uncurry mk_var)) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
        in
            thm(G,A,C)
        end
    else raise simple_fail "bad environment"

fun asml_U (asml:(form list) list) = 
    case asml of 
        [] => []
      | h :: t => op_union (curry eq_form) h (asml_U t)

fun contl_U contl = 
    case contl of 
        [] => HOLset.empty (pair_compare String.compare sort_compare)
      | h :: t => HOLset.union(h,contl_U t)

(*primitive inference rules*)

fun assume f = thm (fvf f,[f],f)

fun conjI (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    thm (contl_U [G1,G2],asml_U [A1,A2],mk_conj C1 C2)
   
fun conjE1 (thm(G,A,C)) = 
    let 
        val (C1,_) = dest_conj C
    in 
        thm (G,A,C1)
    end

fun conjE2 (thm(G,A,C)) = 
    let 
        val (_,C2) = dest_conj C
    in 
        thm (G,A,C2)
    end

fun disjI1 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj C f)

fun disjI2 f (thm (G,A,C)) = thm (contl_U[G,fvf f],A,mk_disj f C)

(**********************************************************************

A |- t1 \/ t2 ,   A1,t1 |- t ,   A2,t2|- t
-------------------------------------------------- disjE
A u A1 u A2 |- t

**********************************************************************)

fun disjE th1 th2 th3 = 
    let val (A,B) = dest_disj(concl th1)
        val _ = eq_form(concl th2, concl th3)
                orelse raise ERR ("disjE.conclsions of th#2, th#3 not equal",[],[],[concl th2,concl th3])
        val _ = fmem A (ant th2) orelse
                raise ERR ("disjE.first disjunct not in the formula list: ",
                           [],[],[A])
        val _ = fmem B (ant th3) orelse
                raise ERR ("disjE.second disjunct not in the formula list: ",
                           [],[],[B])
                
    in
        thm(contl_U [cont th1,cont th2, cont th3],asml_U [ril A (ant th2),ril B (ant th3)],
            concl th3)
    end


fun thml_eq_pairs (th:thm,(ll,rl,asml)) = 
    if is_eq (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])

(*

f = f g = f

coeqo

a:coeqo(f,f) -> X

f o id(A) = f

*)

fun EQ_fsym f thml = 
    case lookup_fun (!fsyms) f of 
        NONE => raise simple_fail ("EQ_fsym.function: " ^ f ^ " is not found")
      | SOME(s,l) => 
        let 
            (*val sl = List.map (fst o dest_eq o concl) thml
            val menv0 = match_tl essps (List.map (uncurry mk_var) l) sl mempty 
            val s' = inst_sort menv0 s *)
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in
            thm (contl_U (List.map cont thml),asml,
                 mk_eq (mk_fun f ll) (mk_fun f rl))
        end

                
fun EQ_psym p thml = 
    case lookup_pred (!psyms) p of 
        NONE => raise simple_fail ("EQ_psym.predicate: " ^ p ^ " is not found")
      | SOME l => 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            (*val _ = match_tl essps (List.map (uncurry mk_var) l) sl mempty 
                    handle _ => raise simple_fail "EQ_psym.the sort list of input is wrong" *)
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            thm (contl_U (List.map cont thml),asml,
                 mk_dimp (mk_pred p ll) (mk_pred p rl))
        end

fun tautI f = thm(fvf f,[],mk_disj f (mk_neg f))

fun negI f (thm (G,A,C)) = 
    let 
        val _ = eq_form(C,FALSE) orelse 
                raise ERR ("negI.concl of thm is not FALSE",
                          [],[],[C])
        val _ = fmem f A orelse
                raise ERR ("negI.formula to be negated not in the asl",
                           [],[],[f])
    in
        thm (G,ril f A, mk_neg f)
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,mk_neg C1) orelse 
                raise ERR ("negE.not a pair of contradiction",
                           [],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                raise simple_fail "falseE.FALSE is not in the asl"
    in
        thm(fvfl (f::fl),fl,f)
    end

        
fun trueI A = thm (fvfl A,A,TRUE)

fun dimpI (thm (G1,A1,I1)) (thm (G2,A2,I2)) =
    let 
        val (f1,f2) = dest_imp I1
        val (f3,f4) = dest_imp I2
        val _ = eq_form(f1,f4) andalso eq_form(f2,f3) orelse
                raise ERR ("dimpI.no match",
                           [],[],[I1,I2])
    in
        thm (contl_U[G1,G2],asml_U[A1,A2],mk_dimp f1 f2)
    end

fun dimpE (thm(G,A,C)) = 
    let
        val (f1,f2) = dest_dimp C
    in
        thm(G,A,mk_conj (mk_imp f1 f2) (mk_imp f2 f1))
    end

fun depends_on (n,s) t = HOLset.member(fvt t,(n,s))

fun allI (ns as (a,s)) (thm(G,A,C)) = (*fun allI ns th*)
    let 
        val G0 = HOLset.delete(G,ns) 
                 handle _ => G
        val D0 = HOLset.listItems $ HOLset.difference(fvs s,G0) (*HOLset.numItems gives size of set, can merge in the variable into G0 and remove this check*)
        val _ = List.length D0 = 0 orelse
                raise ERR ("sort of the variable to be abstract has extra variable(s)",[],List.map var D0,[])
        (*HOLset.isSubset(fvs s,G0) orelse 
          raise simple_fail "sort of the variable to be abstract has extra variable(s)" *)      
        val _ = not (List.exists(fn (n0,s0) => depends_on ns (var (n0,s0))) (HOLset.listItems G0)) orelse (*HOLset.find*)
                raise simple_fail "variable to be abstract occurs in context" 
        val _ = not (HOLset.member(fvfl A,ns)) orelse (*try remove this check since it is contained *)
                raise simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_forall a s C)
    end


(*
fun allI (a,s) (thm(G,A,C)) = 
    let 
        val G0 = HOLset.delete(G,(a,s)) 
                 handle _ => G
        val D0 = HOLset.listItems $ HOLset.difference(fvs s,G0)
        val _ = List.length D0 = 0 orelse
                raise ERR ("sort of the variable to be abstract has extra variable(s)",[],List.map var D0,[])
        (*HOLset.isSubset(fvs s,G0) orelse 
          raise simple_fail "sort of the variable to be abstract has extra variable(s)" *)      
        val _ = not (HOLset.member(fvfl A,(a,s))) orelse
                raise simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_forall a s C)
    end
*)


(**********************************************************************

A,Γ |- !x:s. ϕ(s)
---------------------------------------- allE, requires sort of t is s
A,Γ u (Var(t)) |- ϕ(t)

**********************************************************************)

fun allE t (thm(G,A,C)) = 
    let 
        val (ns as (n,s),b) = dest_forall C
        val _ = sort_of t = s orelse 
                raise ERR ("allE.sorts inconsistent",
                           [s,sort_of t],[mk_var n s,t],[])
    in
        thm(contl_U [G,fvt t],A,substf (ns,t) b)
    end

(**********************************************************************

A,Γ |- f[t/Var(a,s)]
------------------------------ existsI, require sort_of t = s, Var(t) ⊆ Γ
A,Γ |- ?a: s. f

Note: by induction, already have Var(s), Var(t) is subset of G? No, say 
when we want ?a:ob. TRUE from empty cont and assum list.

**********************************************************************)

fun existsI (a,s) t f (thm(G,A,C)) = 
    let 
        val _ = HOLset.isSubset(fvt t,G)
        val _ = (*eq_sort(sort_of t,s)*) sort_of t = s orelse 
                raise simple_fail"term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("existsI.formula has the wrong form, should be something else: ",
                           [],[],[C,substf ((a,s),t) f])
    in
        thm(G,A,mk_exists a s (abstract (a,s) f))
    end


(**********************************************************************

X, Γ1 |- ?x. ϕ(x)        Y, ϕ(a),Γ2 ∪ {a:s0} |- B
-------------------------------------------------- existsE, requires a not in Y and not in B
X,Y, Γ1 ∪ Γ2 |- B

**********************************************************************)

local
    fun delete'(s,e) = HOLset.delete(s,e) handle _ => s 
in
fun existsE (a,s0) (thm(G1,A1,C1)) (thm(G2,A2,C2)) =
    let 
        val ((n,s),b) = dest_exists C1
        val _ = fmem (substf ((n,s),(mk_var a s0)) b) A2
        val _ = (*eq_sort(s,s0)*) s = s0 orelse 
                raise ERR ("the given variable has unexpected sort, should have another sort",[s,s0],[],[])
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (substf ((n,s),(mk_var a s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                raise simple_fail "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,delete'(G2,(a,s0))],
            asml_U[A1,(ril (substf ((n,s),(mk_var a s0)) b) A2)],C2)
    end
end

fun refl t = thm (fvt t,[],mk_eq t t) 

fun sym th = 
    if is_eq (concl th) then 
        let 
            val (l,r) = dest_eq (concl th)
        in thm(cont th,ant th,mk_pred "=" [r,l])
        end
    else raise ERR ("sym.not an equality: ",[],[],[concl th])

fun trans th1 th2 = 
    let 
        val _ = is_eq (concl th1) orelse 
                raise ERR ("trans.first thm not an equality: ",[],[],[concl th1])
        val _ = is_eq (concl th2) orelse
                raise ERR ("trans.second thm not an equality: ",[],[],[concl th2])
        val (t1,t2) = dest_eq (concl th1)
        val (t3,t4) = dest_eq (concl th2)
        val _ = (*eq_term(t2,t3)*) t2 = t3 orelse
                raise ERR ("trans.equalities do not match",[],[],[concl th1,concl th2])
    in 
        thm(contl_U[cont th1,cont th2],
            asml_U[ant th1,ant th2],mk_pred "=" [t1,t4])
    end


(**********************************************************************

A, f1, Γ |- f2
-------------------- disch f1
A, Γ u Var(f1) |- f1 ==> f2

Note: do not require f1 in assumption, if not, add its variables into the context.

**********************************************************************)

fun disch f1 (thm(G,A,f2)) =
        thm (HOLset.union(G,fvf f1),ril f1 A,mk_imp f1 f2)

(**********************************************************************

A1, Γ1 |- A ==> B           A2, Γ2|- A
---------------------------------------- mp
A1 u A2, Γ1 u Γ2 |- B

**********************************************************************)


fun mp (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let
        val (A,B) = dest_imp C1
        val _ = eq_form(C2,A) orelse 
                raise ERR ("mp.no match",[],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U[A1,A2],B) 
    end


(**********************************************************************

A, Γ |- B
-------------------- add_cont Γ'
A, Γ u Γ' |- B

**********************************************************************)

fun add_cont nss th = thm(HOLset.union(cont th,nss),ant th,concl th)

(*
fun subst_term (ot:term) (nt:term) t = 
    if t = ot then nt else 
    case t of 
        Var(n,s) => Var(n,subst_sort ot nt s)
      | Fun(f,s,l) => Fun(f,subst_sort ot nt s,List.map (subst_term ot nt) l)
      | _ => t
and subst_sort ot nt (s:sort) = 
    case s of 
        ar(dom,cod) => ar(subst_term ot nt dom,subst_term ot nt cod)
      | _ => s

fun subst_form ot nt f = 
    case f of
        Pred(p,l) => Pred(p,List.map (subst_term ot nt) l)
      | Conn(co,fl) => Conn(co,List.map (subst_form ot nt) fl)
      | Quant(q,n,s,b) => Quant(q,n,subst_sort ot nt s,subst_form ot nt b)
      | _ => f

fun subst eqn th = 
    let val eqvs = fvf eqn
        val (ot,nt) = dest_eq eqn
        val cont' = HOLset.union(mk_sss (List.map (fvt o (subst_term ot nt) o Var) (HOLset.listItems (cont th))),eqvs)
        val asl' = eqn :: (List.map (subst_form ot nt) (ant th))
        val concl' = subst_form ot nt (concl th)
    in
        thm(cont',asl',concl')
    end
*)

(*
subst (rapf "A = B") (assume (rapf "a: A ->B = c: A ->B") |> add_assum (rapf "A = B"))|> disch_all|>
(C mp) (refl (readt "B")) |> undisch_all

subst (rapf "f:X->A = g:X->A") (assume (rapf "P(f)") |> add_cont (HOLset.union()))|> disch_all|>
(C mp) (refl (readt "B")) |> undisch_all
*)



(*
fun all_distinct l = 
    case l of [] => true
            | h :: ts => if List.exists (fn t => eq_term(t,h)) ts then false
                         else true

fun ukn_psym p = Binarymap.peek (!fpdict,p) = NONE

fun no_ukn_psym f = HOLset.isEmpty (HOLset.filter ukn_psym (psymsf f))

fun ctn_ukn_psym f = (no_ukn_psym f = false)

fun ukn_fsym f = Binarymap.peek (!fpdict,f) = NONE

fun no_ukn_fsym f = HOLset.isEmpty (HOLset.filter ukn_fsym (fsymsf f))

fun ctn_ukn_fsym f = (no_ukn_fsym f = false)

fun define_pred f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_dimp body 
        val (P,args) = dest_pred l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvf r,fvf l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_pred (!psyms) P of 
                    SOME _ =>
                    raise simple_fail("redefining predicate: " ^ P)
                  | _ => ()
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val _ = no_ukn_psym r orelse raise simple_fail"RHS contains unknown predicate"
        val _ = no_ukn_fsym r orelse raise simple_fail"RHS contains unknown function"
        (*check P is a fresh name if not then fail*)
        (*check RHS variables are subset of LHS ones*)
        (*check arguments are all distinct*)
        (*store P in psymd*)
        val _ = new_pred P (List.map dest_var args)
    in thm(essps,[],f)
    end


fun define_fun f = 
    let val fvs = fvf f
        val _ = HOLset.isEmpty fvs orelse raise simple_fail"formula has unexpected free variables"
        val (body,bvs) = strip_forall f 
        val (l,r) = dest_eq body 
        val (nf,sf,args) = dest_fun l 
        val _ = List.all is_var args orelse raise simple_fail"input arguments is not a variable list"
        val _ = HOLset.isSubset (fvt r,fvt l) 
                orelse raise simple_fail"unexpected free variable on RHS"
        val _ = case lookup_fun fsyms0 nf of
                    SOME _ => raise simple_fail("redefining predicate: " ^ nf)
                  | _ => NONE
        val _ = all_distinct args orelse raise simple_fail"input arguments are not all distinct"
        val fsyms0 = new_fun nf (sf,(List.map dest_var args))
    in thm(essps,[],f)
    end



fun subst_t ot nt t = 
    case view_term t of
        vVar(n,s) => if eq_term(t,ot) then nt else var(n,subst_s ot nt s)
      | vFun(f,s,l) => if eq_term(t,ot) then nt else 
                      let val ns = subst_s ot nt s
                          val nl = List.map (subst_t ot nt) l
                      in mk_fun f nl
                      end
      | vB i => t
and subst_s ot nt s = 
    case view_sort s of 
        vo => s
      | va(d,c) => mk_ar_sort (subst_t ot nt d) (subst_t ot nt c)


fun mk_cont nsl =
    List.foldr (fn (new,set) => HOLset.add(set,new)) essps nsl


fun subst_f ot nt f = 
    case view_form f of
        vPred(p,tl) =>
        (mk_pred p (List.map (subst_t ot nt) tl)
         handle e => raise wrap_err "subst_f." e)
      | vConn(co,fl) =>
        (mk_conn co (List.map (subst_f ot nt) fl)
          handle e => raise wrap_err "subst_f." e)
      | vQ(q,n,s,b) =>(mk_quant q n (subst_s ot nt s) 
                                (subst_f ot nt b)
                       handle e => raise wrap_err "subst_f." e)
      | _ => f

(*
fun subst eqth th = 
    let val ctl = HOLset.listItems (HOLset.union(cont th,cont eqth))
        val (obs,ars) = partition (fn (n,s) => s = ob) ctl
        val (names,arss) = unzip ars
        val (ot,nt) = dest_eq (concl eqth)
        val arss' = List.map (substfns ot nt) arss
        val nars = zip names arss'
        val ct' = mk_cont (obs @ nars)
    in thm(ct',asml_U [ant eqth,ant th],concl th)
    end
*)

(*

fun mk_temp th t = 
    let val s = sort_of t
        val t0 = var ("tv0",s)
        val tv = pvariantt (cont th) t0
        val cont' = List.foldr HOLset.union essps 
                               (List.map 
                               (fvt o (subst_t t tv) o var)
                               (HOLset.listItems (cont th)))
        val ant' = List.map (subst_f t tv) (ant th)
        val concl' = subst_f t tv (concl th)
    in (tv,(cont',ant',concl'))
    end


(*AQ : why it see the hd?*)
fun is_ok_temp th (ct0,asl0,w0) t tv = 
    let 
        val tv1 = eq_forml (ant th) (List.map (subst_f tv t) asl0) orelse
      raise ERR ("not a templete, error in assumption list... ",[],[],[hd (ant th),hd (List.map (subst_f tv t) asl0)])
        val tv2 = HOLset.equal(cont th,
                               List.foldr HOLset.union essps 
                               (List.map 
                               (fvt o (subst_t tv t) o var)
                               (HOLset.listItems ct0))) 
                  orelse raise ERR ("not a templete, error incontext... ",[],[],[])
        val tv3 = eq_form (concl th, subst_f tv t w0) orelse
                  raise ERR ("not a templete, error in conclusion",[],[],[concl th, subst_f tv t w0])
    in tv1 andalso tv2 andalso tv3
    end


fun subst eqth (temp as (ct0,asl0,w0)) tv th = 
    let val (ot,nt) = dest_eq $ concl eqth
        val _ = is_ok_temp th temp ot tv orelse 
                raise ERR ("subst.not a templete",[],[],[])
        (*val tv = var $ List.hd $ 
         HOLset.listItems $ HOLset.difference(ct0,cont th)*)
        val ant' = List.map (subst_f tv nt) asl0
        val concl' = subst_f tv nt w0
        val cont' = List.foldr HOLset.union essps 
                               (List.map 
                               (fvt o (subst_t tv nt) o var)
                               (HOLset.listItems ct0))
    in mk_thm (HOLset.union(cont eqth,cont'))
              (asml_U [ant eqth,ant']) concl'
    end 
*)


*)
end
