signature symbols = 
sig
datatype ForP = fsym | psym
val fxty: string -> int
val cdict: (string, pterm_dtype.psort) Binarymap.dict ref
val cdict0: (string, pterm_dtype.psort) Binarymap.dict
val is_const: string -> bool
val ps_of_const: string -> pterm_dtype.psort
val fpdict: (string, ForP) Binarymap.dict ref
val fpdict0: (string, ForP) Binarymap.dict
val insert_fsym: string -> unit
val insert_psym: string -> unit


type fsymd = (string, term.sort * (string * term.sort) list) Binarymap.dict
val fsyms0: fsymd
val fsyms: fsymd ref
val lookup_fun: fsymd -> string -> (term.sort * (string * term.sort) list) option
val is_fun: string -> bool
val new_fun:
   string -> term.sort * (string * term.sort) list -> unit




type psymd = (string, (string * term.sort) list) Binarymap.dict
val psyms0: psymd
val psyms: psymd ref
val lookup_pred: psymd -> string -> (string * term.sort) list option
val is_pred: string -> bool
val new_pred:
   string -> (string * term.sort) list -> unit

end
