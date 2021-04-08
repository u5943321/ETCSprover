use "token.sig";
use "token.sml";
use "term.sig";
use "term.sml";
use "pterm_dtype.sml";
use "form.sig";
use "form.sml";
use "pterm.sig";
use "pterm.sml";
use "thm.sig";
use "thm.sml";
use "conv.sig"; 
use "conv.sml";
(*
use "tactic.sig";
use "tactic.sml"
*)
open thm form term;
val vs = fvf (concl o_assoc);
