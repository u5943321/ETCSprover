signature conv = 
sig
type form = form.form
type term = term.term
type sort = term.sort
type thm = thm.thm
type conv = abbrev.conv
type fconv = abbrev.fconv

val all_conv: conv
val all_fconv: fconv
val arg_conv: conv -> conv
val depth_conv: conv -> conv
val first_conv: conv list -> conv
val no_conv: conv
val orelsec: conv * conv -> conv
val part_fmatch: (thm -> form) -> thm -> fconv
val part_tmatch: (thm -> term) -> thm -> conv
val redepth_conv: conv -> conv
val repeatc: conv -> conv
val rewr_conv: thm -> conv
val rewr_fconv: thm -> fconv
val sub_conv: conv -> conv
val thenc: conv * conv -> conv
val thenfc: fconv * fconv -> fconv
val top_depth_conv: conv -> conv
val once_depth_conv: conv -> conv
val try_conv: conv -> conv
exception unchanged
val basic_fconv: conv -> fconv -> fconv
val basic_taut_fconv: fconv
val changed_fconv: fconv -> fconv
val conj_fconv: fconv -> fconv 
val depth_fconv: conv -> fconv -> fconv
val dimp_fconv: fconv -> fconv
val disj_fconv: fconv -> fconv
val first_fconv: fconv list -> fconv
val imp_fconv: fconv -> fconv
val no_fconv: fconv
val orelsefc: fconv * fconv -> fconv
val pred_fconv: conv -> fconv
val redepth_fconv: conv -> fconv -> fconv
val refl_fconv: fconv
val repeatfc: fconv -> fconv
val sub_fconv: conv -> fconv -> fconv
val taut_conj_fconv: fconv
val taut_dimp_fconv: fconv
val taut_disj_fconv: fconv
val taut_exists_fconv: fconv
val taut_forall_fconv: fconv
val taut_imp_fconv: fconv
val top_depth_fconv: conv -> fconv -> fconv
val once_depth_fconv: conv -> fconv -> fconv
val basic_once_fconv: conv -> fconv -> fconv
val try_fconv: fconv -> fconv
val simp_trace: bool ref
val conv_rule: fconv -> thm -> thm
val GSYM: thm -> thm
val right_imp_forall_fconv: fconv
val sym_fconv: fconv
end
