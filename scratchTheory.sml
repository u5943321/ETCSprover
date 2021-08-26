structure scratchTheory :> scratchTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading scratchTheory ... "
    else ()
  
  open Type Term Thm
  local open indexedListsTheory patternMatchesTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "scratch"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/ETCSprover/scratchTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op Forall_def _ = () val op Forall_def = TDB.find "Forall_def"
  fun op rcomp _ = () val op rcomp = TDB.find "rcomp"
  fun op reducible _ = () val op reducible = TDB.find "reducible"
  fun op functional _ = () val op functional = TDB.find "functional"
  fun op stepFunction _ = () val op stepFunction = TDB.find "stepFunction"
  fun op computable _ = () val op computable = TDB.find "computable"
  fun op classical _ = () val op classical = TDB.find "classical"
  fun op Forall2_def _ = () val op Forall2_def = TDB.find "Forall2_def"
  fun op terminatesOn_def _ = ()
  val op terminatesOn_def = TDB.find "terminatesOn_def"
  fun op evaluates_def _ = ()
  val op evaluates_def = TDB.find "evaluates_def"
  fun op normalizes _ = () val op normalizes = TDB.find "normalizes"
  fun op size_induction _ = ()
  val op size_induction = TDB.find "size_induction"
  fun op nth_error_ind _ = ()
  val op nth_error_ind = TDB.find "nth_error_ind"
  fun op nth_error _ = () val op nth_error = TDB.find "nth_error"
  fun op nth_error_compute _ = ()
  val op nth_error_compute = TDB.find "nth_error_compute"
  fun op nth_error_lt_Some _ = ()
  val op nth_error_lt_Some = TDB.find "nth_error_lt_Some"
  fun op nth_error_Some_lt _ = ()
  val op nth_error_Some_lt = TDB.find "nth_error_Some_lt"
  fun op nth_error_map _ = ()
  val op nth_error_map = TDB.find "nth_error_map"
  fun op Forall_rules _ = () val op Forall_rules = TDB.find "Forall_rules"
  fun op Forall_ind _ = () val op Forall_ind = TDB.find "Forall_ind"
  fun op Forall_strongind _ = ()
  val op Forall_strongind = TDB.find "Forall_strongind"
  fun op Forall_cases _ = () val op Forall_cases = TDB.find "Forall_cases"
  fun op Forall_map _ = () val op Forall_map = TDB.find "Forall_map"
  fun op computable_classical _ = ()
  val op computable_classical = TDB.find "computable_classical"
  fun op Forall2_rules _ = ()
  val op Forall2_rules = TDB.find "Forall2_rules"
  fun op Forall2_ind _ = () val op Forall2_ind = TDB.find "Forall2_ind"
  fun op Forall2_strongind _ = ()
  val op Forall2_strongind = TDB.find "Forall2_strongind"
  fun op Forall2_cases _ = ()
  val op Forall2_cases = TDB.find "Forall2_cases"
  fun op Forall2_impl _ = () val op Forall2_impl = TDB.find "Forall2_impl"
  fun op terminatesOn_rules _ = ()
  val op terminatesOn_rules = TDB.find "terminatesOn_rules"
  fun op terminatesOn_ind _ = ()
  val op terminatesOn_ind = TDB.find "terminatesOn_ind"
  fun op terminatesOn_strongind _ = ()
  val op terminatesOn_strongind = TDB.find "terminatesOn_strongind"
  fun op terminatesOn_cases _ = ()
  val op terminatesOn_cases = TDB.find "terminatesOn_cases"
  fun op evaluates_rules _ = ()
  val op evaluates_rules = TDB.find "evaluates_rules"
  fun op evaluates_ind _ = ()
  val op evaluates_ind = TDB.find "evaluates_ind"
  fun op evaluates_strongind _ = ()
  val op evaluates_strongind = TDB.find "evaluates_strongind"
  fun op evaluates_cases _ = ()
  val op evaluates_cases = TDB.find "evaluates_cases"
  fun op evaluates_fun _ = ()
  val op evaluates_fun = TDB.find "evaluates_fun"
  fun op irred_evaluates_refl _ = ()
  val op irred_evaluates_refl = TDB.find "irred_evaluates_refl"
  fun op normalizes_terminates0 _ = ()
  val op normalizes_terminates0 = TDB.find "normalizes_terminates0"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "scratch"

end
