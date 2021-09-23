signature parser = 
sig
datatype psort = datatype pterm_dtype.psort   
datatype pterm = datatype pterm_dtype.pterm
datatype pform = datatype pterm_dtype.pform
type sort = term.sort
type term = term.term
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

val rapf: string -> form.form
val rastt: string -> term.term

val pwct: (string * sort) set -> string -> term
val pwcf: (string * sort) set -> string -> form

val readfq: 'a frag list -> form
end
