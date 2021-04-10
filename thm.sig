signature thm = 
sig
type form = form.form
type term = term.term
type sort = term.sort
datatype thm = thm of form list * form
val assume: form -> thm
val refl: term -> thm
val concl: thm -> form
val trans: thm -> thm -> thm
val sym: thm -> thm
val ant: thm -> form list
val conjI: thm  -> thm -> thm
val disjI1: thm -> form -> thm
val disjI2: form -> thm -> thm
val dimpI: thm -> thm -> thm
val dimpE1: thm -> form -> thm
val dimpE2: thm -> form -> thm
val EQ_fsym: string -> sort -> thm list -> thm
val EQ_psym: string -> thm list -> thm
val conjE1: thm -> thm
val conjE2: thm -> thm
val disjE: form -> form -> form -> thm -> thm -> thm -> thm
val tautI: form -> thm
val negI: thm -> form -> thm
val negE: thm -> thm -> thm
val existsE: thm -> (string * sort) -> thm
val existsI: thm -> (string * sort) -> term -> form -> thm
val simple_exists: (string  * sort) -> thm -> thm
val falseE: form -> thm
val trueI: form list -> thm
val allI: (string * sort) -> thm -> thm
val allE: thm -> term -> thm
val disch: form -> thm -> thm
val mp: thm -> thm -> thm
val undisch: thm -> thm
val add_assum: form -> thm -> thm
val imp_trans: thm -> thm -> thm
val frefl: form -> thm
val dimpl2r: thm -> thm
val dimpr2l: thm -> thm
val iff_trans: thm -> thm -> thm
val equivT: thm -> thm
val idL: thm
val idR: thm
val o_assoc: thm
val ax1_1: thm
val ax1_2: thm
val ax1_3: thm
val ax1_4: thm
val ax1_5: thm
val ax1_6: thm
val ax2: thm
val ax3: thm
val ax4: thm
val ax5: thm
(*type thm*)
(*rules for inference*) 
end
