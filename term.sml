datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * string list
    | Bound of int
    | Fun of string * term list;

val one = Fun ("one",[])
val zero = Fun ("zero",[])                                              

exception no_sort 

fun po_i A B = Fun ("po",[A,B]) 

fun pa_i f g = Fun ("pa",[f,g])

fun sort_of t =  
    case t of Fun ("one",[]) => ob
            | Fun ("to1",[X]) => ar (X,one)
            | Fun ("zero",[]) => ob
            | Fun ("from0",[X]) => ar (zero,X) 
            | Fun ("o",[g,f]) => (case (sort_of g, sort_of f) of 
                                      (ar (_,C), ar (A,_)) => ar (A,C)
                                    | _ => raise no_sort)
            | Fun ("po",[A,B]) => ob
            | Fun ("p1",[A,B]) => ar (po_i A B,A)                                                             | Fun ("p2",[A,B]) => ar (po_i A B,B)
            | Fun ("pa",[f,g]) => (case (sort_of f, sort_of g) of 
                                       (ar (C1,A), ar (C2,B)) => ar (C1,po_i A B)
                                     | _ => raise no_sort)   

            | _ => ob


fun po A B = if sort_of A = ob andalso sort_of B = ob then po_i A B
             else raise no_sort 

fun p1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p1",[A,B])
             else raise no_sort 

fun p2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p2",[A,B])
             else raise no_sort 

fun to1 X = if sort_of X = ob then Fun ("to1",[X]) else raise no_sort

fun from0 X = if sort_of X = ob then Fun ("form0",[X]) else raise no_sort

fun pa f g = (case (sort_of g, sort_of f) of 
                       (ar (C1,A), ar (C2,B)) => if C1 = C2 then pa_i f g
                                                 else raise no_sort
                                     | _ => raise no_sort)


infix O
fun O_i f g = Fun ("o",[f,g])
fun op O (f,g) = (case (sort_of g, sort_of f) of 
                       (ar (B2,C), ar (A,B1)) => if B1 = B2 then O_i f g
                                                 else raise no_sort
                                     | _ => raise no_sort)


datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;     


(******)
datatype sort = ob 
               | ar of term * term 
and term =
    Var of string * sort
    | Param of string * string list
    | Bound of int
    | Fun of string * term list;

val one = Fun ("one",[])
val zero = Fun ("zero",[])                                              

exception no_sort 

fun po_i A B = Fun ("po",[A,B]) 

fun po A B = if sort_of A = ob andalso sort_of B = ob then po_i A B
             else raise no_sort 

fun p1 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p1",[A,B])
             else raise no_sort 

fun p2 A B = if sort_of A = ob andalso sort_of B = ob then Fun ("p2",[A,B])
             else raise no_sort 

fun to1 X = if sort_of X = ob then Fun ("to1",[X]) else raise no_sort

fun from0 X = if sort_of X = ob then Fun ("form0",[X]) else raise no_sort

fun pa_i f g = Fun ("pa",[f,g])

fun pa f g = (case (sort_of g, sort_of f) of 
                       (ar (C1,A), ar (C2,B)) => if C1 = C2 then pa_i f g
                                                 else raise no_sort
                                     | _ => raise no_sort)


infix O
fun O_i f g = Fun ("o",[f,g])
fun op O (f,g) = (case (sort_of g, sort_of f) of 
                       (ar (B2,C), ar (A,B1)) => if B1 = B2 then O_i f g
                                                 else raise no_sort
                                     | _ => raise no_sort)

fun sort_of t =  
    case t of Fun ("one",[]) => ob
            | Fun ("to1",[X]) => ar (X,one)
            | Fun ("zero",[]) => ob
            | Fun ("from0",[X]) => ar (zero,X) 
            | Fun ("o",[g,f]) => (case (sort_of g, sort_of f) of 
                                      (ar (_,C), ar (A,_)) => ar (A,C)
                                    | _ => raise no_sort)
            | Fun ("po",[A,B]) => ob
            | Fun ("p1",[A,B]) => ar (po_i A B,A)                                                             | Fun ("p2",[A,B]) => ar (po_i A B,B)
            | Fun ("pa",[f,g]) => (case (sort_of f, sort_of g) of 
                                       (ar (C1,A), ar (C2,B)) => ar (C1,po_i A B)
                                     | _ => raise no_sort)   

            | _ => ob

datatype form =
Pred of string * term list
| Conn of string * form list
| Quant of string * string * sort * form;           
                                 

(*
fun sort_check t s = 
    case t of Fun ("one",[]) => s = ob
            | Fun ("to1",[X]) => s = ar (X,one) andalso sort_check X ob
            | Fun ("zero",[]) => s = ob
            | Fun ("from0",[X]) => s = ar (zero,X) andalso sort_check X ob
            | Fun ("o",[]) => 
*)
