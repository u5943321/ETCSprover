use "infixes.sml";
use "token.sig";
use "token.sml";
use "pterm_dtype.sml";
use "term.sig";
use "term.sml";

use "form.sig";
use "form.sml";
use "symbols.sig";
use "symbols.sml";

use "pterm.sig";
use "pterm.sml";

use "logic.sig";
use "logic.sml";

open term form symbols pterm logic;

use "drule.sig";
use "drule.sml";
open drule;

use "abbrev.sig";
use "abbrev.sml";

use "conv.sig"; 
use "conv.sml";
open abbrev conv;


use "tactic.sig";
use "tactic.sml";

open tactic;

(*
use "thm.sig";
use "thm.sml";
use "drule.sig";
use "drule.sml";

open term form pterm thm drule symbols;



use "pp.sig"; 
use "pp.sml";

open pp;






use "tactic.sig";
use "tactic.sml";

open tactic;


use "goalstack.sig";
use "goalstack.sml";

open goalstack;
(*
use "proofmanager.sml";
open proofmanager;

*)
*)

