structure symbols :> symbols = 
struct
open term form pterm_dtype

exception ERROR of string

fun fxty i = 
    case i of 
        ":" =>(* 460 *) 900
      | "->" =>(* 470 *) 900
      | "=" => 450
      | "==>" => 200
      | "<=>" => 100
      | "~" => 900
      | "&" => 400
      | "|" => 300
      | "*" => 600
      | "+" => 500
      | "^" => 700
      | "o" => 800
      | _ => ~1

type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict

type psymd = (string, (string * sort) list) Binarymap.dict


fun lookup_pred (pd:psymd) p = Binarymap.peek (pd,p)

fun lookup_fun (fd:fsymd) f = Binarymap.peek (fd,f)


val psyms0:psymd = List.foldr (fn ((p:string,l:(string * sort) list),d) =>
                                  Binarymap.insert (d,p,l)) 
                        (Binarymap.mkDict String.compare)
                        [(*("ismono",[("a",ar(mk_ob "A",mk_ob "B"))]),*)
                         ("isgroup",[("G",ob),
                                     ("m",ar (mk_fun "*" ob [mk_ob "G",mk_ob "G"],
                                              mk_ob "G")),
                                     ("i",ar (mk_fun "1" ob [],mk_ob "G")),
                                     ("inv",ar (mk_ob "G",mk_ob "G"))]),
                         ("=",[("A",ob),("B",ob)]),
                         ("=",[("a",ar(mk_ob "A",mk_ob "B")),("b",ar(mk_ob "A",mk_ob "B"))])]


type fsymd = (string, sort * ((string * sort) list)) Binarymap.dict

val fsyms0:fsymd =  
    List.foldr 
        (fn ((p:string,(s:sort,l:(string * sort) list)),d) =>
            Binarymap.insert (d,p,(s,l)))
        (Binarymap.mkDict String.compare)
        [("N",(ob,[])),
         ("0",(ob,[])),
         ("1",(ob,[])),
         ("id",(ar(mk_ob "A",mk_ob "A"),[("A",ob)])),
         ("to1",(ar(mk_ob "X",mk_ob "one"),
                 [("one",ob),("X",ob)])),
         ("from0",(ar(mk_ob "zero",mk_ob "X"),
                   [("zero",ob),("X",ob)])),
         ("o",(ar(mk_ob "A",mk_ob "C"),[("f",ar(mk_ob "B",mk_ob "C")),
                                        ("g",ar(mk_ob "A",mk_ob "B"))])),
         ("*",(ob,[("A",ob),("B",ob)])),
         ("+",(ob,[("A",ob),("B",ob)]))](*,
         ("p1",(ar(mk_fun "*" ob [mk_ob "A",mk_ob "B"],mk_ob "A"),[("A",ob),("B",ob)])),
         ("p2",(ar(mk_fun "*" ob [mk_ob "A",mk_ob "B"],mk_ob "B"),[("A",ob),("B",ob)])),
         ("i1",(ar(mk_ob "A",mk_fun "+" ob [mk_ob "A",mk_ob "B"]),[("A",ob),("B",ob)])),
         ("i2",(ar(mk_ob "B",mk_fun "+" ob [mk_ob "A",mk_ob "B"]),[("A",ob),("B",ob)])),
         ("pa",(ar(mk_ob "X",mk_fun "*" ob [mk_ob "A",mk_ob "B"]),
                [("f",ar(mk_ob "X",mk_ob "A")),("g",ar(mk_ob "X",mk_ob "B"))])),
         ("copa",(ar(mk_fun "+" ob [mk_ob "A",mk_ob "B"],mk_ob "X"),
                [("f",ar(mk_ob "A",mk_ob "X")),("g",ar(mk_ob "B",mk_ob "X"))])),
         ("eqo",(ob,[("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("coeqo",(ob,[("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("eqa",(ar(mk_fun "eqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"],mk_ob "A"),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("coeqa",(ar(mk_ob "B",mk_fun "coeqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"]),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B"))])),
         ("eqinduce",(ar(mk_ob "X",mk_fun "eqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"]),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B")),
                  ("h",ar(mk_ob "X",mk_ob "A"))])),
         ("coeqinduce",(ar(mk_fun "coeqo" ob [mk_ar0 "f" "A" "B",mk_ar0 "g" "A" "B"],mk_ob "X"),
                 [("f",ar(mk_ob "A",mk_ob "B")),("g",ar(mk_ob "A",mk_ob "B")),
                  ("h",ar(mk_ob "B",mk_ob "X"))])),
         ("exp",(ob,[("A",ob),("B",ob)])),
         ("tp",(mk_ar_sort (mk_ob "B") (mk_fun "exp" ob [mk_ob "A", mk_ob "C"]),
                [("f",ar(mk_fun "*" ob [mk_ob "A", mk_ob "B"],mk_ob "C"))])),
         ("ev",(mk_ar_sort 
                    (mk_fun "*" ob [mk_ob "A",mk_fun "exp" ob [mk_ob "A",mk_ob "B"]]) 
                    (mk_ob "B"),
                [("A",ob),("B",ob)])),
         ("s",(ar(mk_const "N" ob,mk_const "N" ob),[])),
         ("z",(ar(mk_const "1" ob,mk_const "N" ob),[])),
         ("Nind",(ar(mk_const "N" ob,mk_ob "X"),
                  [("x0",ar(mk_const "1" ob,mk_ob "X")),
                   ("t",ar(mk_ob "X",mk_ob "X"))]))
        ]
*)
val cdict0:(string,psort) Binarymap.dict =
    List.foldr (fn ((n,s),d) => (Binarymap.insert(d,n,s))) 
               (Binarymap.mkDict String.compare) 
               [("N",pob),("0",pob),("1",pob),("z",par(pFun("1",pob,[]),pFun("N",pob,[]))),
                ("s",par(pFun("N",pob,[]),pFun("N",pob,[])))]

val cdict = ref cdict0

fun is_const sr = 
    case (Binarymap.peek (!cdict,sr)) of 
        SOME _ => true
      | _ => false

fun ps_of_const c = 
    case (Binarymap.peek (!cdict,c)) of 
        SOME ps => ps 
      | _ => raise ERROR "not a constant"

datatype ForP = fsym | psym

val fpdict0:(string,ForP) Binarymap.dict =
    foldr (fn ((n,forp),d) => Binarymap.insert(d,n,forp)) (Binarymap.mkDict String.compare) 
          [("=",psym),(*"\cong",psym*) ("T",psym),("F",psym),
           ("P",psym),("Q",psym),("R",psym),("S",psym),
           ("ismono",psym),("isgroup",psym),("ismem",psym),("areiso",psym),
           ("o",fsym),("id",fsym),
           ("to1",fsym),("from0",fsym),
           ("p1",fsym),("p2",fsym),("pa",fsym),("po",fsym),
           ("i1",fsym),("i2",fsym),("copa",fsym),("copo",fsym),
           ("eqo",fsym),("eqa",fsym),("coeqo",fsym),("coeqa",fsym),
           ("*",fsym),("+",fsym),("^",fsym),
           ("exp",fsym),("ev",fsym),("tp",fsym),
           ("eqinduce",fsym),("coeqinduce",fsym),("Nind",fsym)
           ]

(*change to fold*)

val fpdict = ref fpdict0
val fsyms = ref fsyms0
val psyms = ref psyms0

fun insert_fsym s = fpdict:= Binarymap.insert(!fpdict,s,fsym) 
fun insert_psym s = fpdict:= Binarymap.insert(!fpdict,s,psym)


fun is_fun sr = 
    case (Binarymap.peek (!fpdict,sr)) of 
        SOME fsym => true
      | _ => false

fun is_pred sr =
    case (Binarymap.peek (!fpdict,sr)) of
        SOME psym => true
      | _ => false


fun new_pred p tl = psyms := Binarymap.insert (!psyms,p,tl)

fun new_fun f (s,tl) = fsyms := Binarymap.insert (!fsyms,f,(s,tl))

end
