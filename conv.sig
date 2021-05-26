signature conv = 
sig
type form = form.form
type term = term.term
type sort = term.sort

val all_conv: term -> thm
val all_fconv: form -> thm
val arg_conv: (term -> thm) -> term -> thm
type conv = term -> thm
val depth_conv: (term -> thm) -> term -> thm
val first_conv: ('a -> 'b) list -> 'a -> 'b
val no_conv: 'a -> 'b
val orelsec: ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
val part_fmatch: (thm -> form) -> thm -> form -> thm
val part_tmatch: (thm -> term) -> thm -> term -> thm
val redepth_conv: (term -> thm) -> term -> thm
val repeatc: (term -> thm) -> term -> thm
val rewr_conv: thm -> term -> thm
val rewr_fconv: thm -> form -> thm
val sub_conv: (term -> thm) -> term -> thm
val thenc: ('a -> thm) * (term -> thm) -> 'a -> thm
val thenfc: ('a -> thm) * (form -> thm) -> 'a -> thm
val top_depth_conv: (term -> thm) -> term -> thm
val try_conv: (term -> thm) -> term -> thm
exception unchanged
val assum_list:
   (thm list -> form list * 'a -> 'b) -> form list * 'a -> 'b
val basic_fconv: (term -> thm) -> (form -> thm) -> form -> thm
val basic_taut_fconv: form -> thm
val changed_fconv: (form -> thm) -> form -> thm
val conj_fconv: (form -> thm) -> form -> thm
val depth_fconv: (term -> thm) -> (form -> thm) -> form -> thm
val dimp_fconv: (form -> thm) -> form -> thm
val disj_fconv: (form -> thm) -> form -> thm
val first_fconv: ('a -> 'b) list -> 'a -> 'b
val imp_fconv: (form -> thm) -> form -> thm
val no_fconv: 'a -> 'b
val orelsefc: ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
val pred_fconv: (term -> thm) -> form -> thm
val redepth_fconv: (term -> thm) -> (form -> thm) -> form -> thm
val refl_fconv: form -> thm
val repeatfc: (form -> thm) -> form -> thm
val sub_fconv: (term -> thm) -> (form -> thm) -> form -> thm
val taut_conj_fconv: form -> thm
val taut_dimp_fconv: form -> thm
val taut_disj_fconv: form -> thm
val taut_exists_fconv: form -> thm
val taut_forall_fconv: form -> thm
val taut_imp_fconv: form -> thm
val top_depth_fconv: (term -> thm) -> (form -> thm) -> form -> thm
val try_fconv: (form -> thm) -> form -> thm

end
