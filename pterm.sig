signature pterm = 
sig
datatype psort = datatype pterm_dtype.psort   
datatype pterm = datatype pterm_dtype.pterm
datatype pform = datatype pterm_dtype.pform
structure Env: sig 
    type env
    val empty : env
    val insert_ps: string -> psort -> env -> env
    val insert_pt: string -> pterm -> env -> env
    val dps_of: env -> (string,psort)Binarymap.dict 
    val dpt_of: env -> (string,pterm)Binarymap.dict 
    val fresh_var: env -> string * env
    val lookup_pt: env -> string -> pterm option
    val lookup_ps: env -> string -> psort option
end
val read_pt : string -> pterm * Env.env
val read_pf : string -> pform * Env.env
val read_t : string -> term.term * (string list * string list * string list * int)
val read_f : string -> form.form * (string list * string list * string list * int)
end
