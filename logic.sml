structure logic :> logic = 
struct
open token pterm_dtype term form pterm symbols

datatype thm = thm of ((string * sort) set * form list * form) 
exception ERR of string * sort list * term list * form list

fun dest_thm (thm(G,A,C)) = (G,A,C)

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
            val G = mk_sss (List.map (fvt o (inst_term env) o Var) G0)
            val A = List.map (inst_form env) (ant th)
            val C = inst_form env (concl th)
        in
            thm(G,A,C)
        end
    else simple_fail "bad environment"

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
    thm (contl_U [G1,G2],asml_U [A1,A2],Conn ("&",[C1,C2]))
   
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

fun disjI1 f (thm (G,A,C)) = thm (G,A,Conn ("|",[C,f]))

fun disjI2 f (thm (G,A,C)) = thm (G,A,Conn ("|",[f,C]))

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
    if is_eqn (concl th) then  
        let 
            val (l,r) = dest_eq (concl th)
            val asm = ant th
        in 
            (l::ll,r::rl,asml_U [asm,asml])
        end
    else 
        raise ERR ("thml_eq_pairs.input thm is not an equality: ",
                   [],[],[concl th])



fun EQ_fsym f thml = 
    case lookup_fun fsyms0 f of 
        NONE => simple_fail ("EQ_fsym.function: " ^ f ^ " is not found")
      | SOME(s,l) => 
        let 
            val sl = List.map (fst o dest_eq o concl) thml
            val menv0 = match_tl essps (List.map Var l) sl mempty 
            val s' = inst_sort menv0 s
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in
            thm (contl_U (List.map cont thml),asml,
                 Pred("=",[Fun(f,s',ll),Fun(f,s',rl)]))
        end
                
fun EQ_psym p thml = 
    case lookup_pred psyms0 p of 
        NONE => simple_fail ("EQ_psym.predicate: " ^ p ^ " is not found")
      | SOME _ => 
        let 
            val (ll,rl,asml) = List.foldr thml_eq_pairs ([],[],[]) thml
        in 
            thm (contl_U (List.map cont thml),asml,
                 Conn("<=>",[Pred(p,ll),Pred(p,rl)]))
        end

fun tautI f = thm(fvf f,[],Conn("|",[f,mk_neg f]))

fun negI f (thm (G,A,C)) = 
    let 
        val _ = (C = FALSE) orelse 
                raise ERR ("negI.concl of thm is not FALSE",
                          [],[],[C])
        val _ = fmem f A orelse
                raise ERR ("negI.formula to be negated not in the asl",
                           [],[],[f])
    in
        thm (G,ril f A, (Conn("~",[f])))
    end

fun negE (thm (G1,A1,C1)) (thm (G2,A2,C2)) = 
    let 
        val _ = eq_form(C2,Conn("~",[C1])) orelse 
                eq_form(C1,Conn("~",[C2])) orelse
                raise ERR ("negE.not a pair of contradiction",
                           [],[],[C1,C2])
    in
        thm (contl_U [G1,G2],asml_U [A1,A2],FALSE)
    end

fun falseE fl f = 
    let val _ = fmem FALSE fl orelse 
                simple_fail "falseE.FALSE is not in the asl"
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
        thm (contl_U[G1,G2],asml_U[A1,A2],Conn("<=>",[f1,f2]))
    end

fun dimpE (thm(G,A,C)) = 
    let
        val (f1,f2) = dest_dimp C
    in
        thm(G,A,Conn("&", 
             [Conn("==>",[f1,f2]),Conn("==>",[f2,f1])]))
    end


fun allI (a,s) (thm(G,A,C)) = 
    let 
        val G0 = HOLset.delete(G,(a,s)) 
                 handle _ => G
        val _ = HOLset.isSubset(fvs s,G0) orelse 
                simple_fail "sort of the variable to be abstract has extra variable(s)"
        val _ = not (HOLset.member(fvfl A,(a,s))) orelse
                simple_fail "variable to be abstract occurs in assumption" 
    in thm(G0,A,mk_all a s C)
    end



(**********************************************************************

A,Γ |- !x:s. ϕ(s)
---------------------------------------- allE, requires sort of t is s
A,Γ u (Var(t)) |- ϕ(t)

**********************************************************************)

fun allE t (thm(G,A,C)) = 
    let 
        val ((n,s),b) = dest_all C
        val _ = (sort_of t = s) orelse 
                raise ERR ("allE.sorts inconsistent",
                           [s,sort_of t],[Var(n,s),t],[])
    in
        thm(contl_U [G,fvt t],A,subst_bound t b)
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
        val _ = (sort_of t = s) orelse 
                simple_fail"term and variable to be abstract of different sorts"
        val _ = eq_form (C, substf ((a,s),t) f) orelse
                raise ERR ("existsI.formula has the wrong form, should be something else: ",
                           [],[],[C,substf ((a,s),t) f])
    in
        thm(G,A,Quant("?",a,s,abstract (a,s) f))
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
        val _ = fmem (subst_bound (Var(a,s0)) b) A2
        val _ = (s = s0) orelse 
                raise ERR ("the given variable has unexpected sort, should have another sort",[s,s0],[],[])
        val _ = (HOLset.member
                     (HOLset.union
                          (fvfl (ril (subst_bound (Var(a,s0)) b) A2),
                           fvf C2),(a,s0)) = false) orelse
                simple_fail "the given variable occurs unexpectedly"
    in
        thm(contl_U[G1,delete'(G2,(a,s0))],
            asml_U[A1,(ril (subst_bound (Var(a,s0)) b) A2)],C2)
    end
end

fun refl t = thm (fvt t,[],(Pred("=",[t,t]))) 

fun sym th = 
    if is_eqn (concl th) then 
        let 
            val (l,r) = dest_eq (concl th)
        in thm(cont th,ant th,Pred("=",[r,l]))
        end
    else raise ERR ("sym.not an equality: ",[],[],[concl th])

fun trans th1 th2 = 
    let 
        val _ = is_eqn (concl th1) orelse 
                raise ERR ("trans.first thm not an equality: ",[],[],[concl th1])
        val _ = is_eqn (concl th2) orelse
                raise ERR ("trans.second thm not an equality: ",[],[],[concl th2])
        val (t1,t2) = dest_eq ((fst o strip_all) (concl th1))
        val (t3,t4) = dest_eq ((fst o strip_all) (concl th2))
        val _ = (t2 = t3) orelse
                raise ERR ("trans.equalities do not match",[],[],[concl th1,concl th2])
    in 
        thm(contl_U[cont th1,cont th2],
            asml_U[ant th1,ant th2],Pred("=",[t1,t4]))
    end


(**********************************************************************

A, f1, Γ |- f2
-------------------- disch f1
A, Γ u Var(f1) |- f1 ==> f2

Note: do not require f1 in assumption, if not, add its variables into the context.

**********************************************************************)

fun disch f1 (thm(G,A,f2)) =
        thm (HOLset.union(G,fvf f1),ril f1 A,Conn ("==>",[f1,f2]))

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


end
