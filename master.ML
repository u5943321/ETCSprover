use "term.sig";
use "term.sml";
use "form.sig";
use "form.sml";
use "logic.sig";
use "logic.sml";

open term form logic;

use "pp.sig";
use "pp.sml";

open pp;

use "token.sig";
use "token.sml";
use "pterm_dtype.sml";
use "pterm.sig";
use "pterm.sml";

open token pterm_dtype pterm;

use "drule.sig";
use "drule.sml";
open drule;

use "infixes.sml";
use "abbrev.sig";
use "abbrev.sml";

open abbrev;

use "conv.sig"; 
use "conv.sml";
use "tactic.sig";
use "tactic.sml";

open conv tactic;

use "goalstack.sig";
use "goalstack.sml";

open goalstack;

(*

use "infixes.sml";
use "token.sig";
use "token.sml";
use "pterm_dtype.sml";
use "term.sig";
use "term.sml";
use "form.sig";
use "form.sml";
use "pterm.sig";
use "pterm.sml";
use "logic.sig";
use "logic.sml";
use "pp.sig";
use "pp.sml";




(*put term form logic first, since they are in kernel

token pterm_dtype pterm not in kernel, use it after the kernel
*)

use "drule.sig";
use "drule.sml";

use "abbrev.sig";
use "abbrev.sml";
use "conv.sig"; 
use "conv.sml";
use "tactic.sig";
use "tactic.sml";


use "goalstack.sig";
use "goalstack.sml";

open term form pterm logic pp conv tactic goalstack;
*)
