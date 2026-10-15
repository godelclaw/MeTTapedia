import Mettapedia.Logic.HostingStyles.PrimeCandidate.SpaceExtension
import Mettapedia.Logic.HostingStyles.Guests.MM0Checker

/-!
# The candidate with a space as a term, and the check with its contexts

The candidate with a run constructor, a space that is a term and a variable
atom (`spacePresentation`) is the presentation under which a matching
evaluator hosts theories of first-order rule instances on terms.  It adds
constructors of spaces and atoms and no rewrite and no equation, so it still
reduces in the sort of processes alone (`probeWithSpace_separateProcess`).

Hence, **under every evaluator of its premises, it hosts with contexts no
check that has a step** (`space_checkerWithContexts_row`), the checker of
every MM0 theory among them (`space_mm0CheckerWithContexts_row`): no map at
all with its contexts as they are, no map that preserves steps under the
reading with regions, no hosting map under any reading.

Whether that presentation, under the matching evaluator or another fixed
evaluator, hosts or runs the checker of an MM0 theory on terms is not settled
here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Presentation.Calculus
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings

/-- **The candidate with a space as a term reduces in the sort of processes
alone**: its rewrites are headed by constructors of processes, no constructor
takes a process, and quotation and dropping are no constructors of
processes. -/
theorem probeWithSpace_separateProcess :
    rewritesHeadedIn probeWithSpace ["Process"] = true ∧
      takesNoneOf probeWithSpace "Process" = true ∧
        sortLabels probeWithSpace "Process" "prime-quote" = false ∧
          sortLabels probeWithSpace "Process" "prime-drop" = false := by
  decide

/-- **Negative**, for the shape: it takes atoms in its spaces, so the sort of
atoms is not separate. -/
theorem probeWithSpace_takes_atoms : takesNoneOf probeWithSpace "Atom" = false := by
  decide

/-- **The candidate with a space as a term and the check with its contexts**,
for a check that has a step and under every evaluator of its premises: no map
at all with its contexts as they are; no map that preserves steps under the
reading in which atoms and names are data; no hosting map under any
reading. -/
theorem space_checkerWithContexts_row {K : AuthoredCalculus} (base : BasePremiseEvaluator)
    {state next : Checking K} (step : CheckStep K state next) :
    IsEmpty (ContextMap (checkerWithContexts K) (contextTheory base spacePresentation)) ∧
      (∀ map : ContextMap (checkerWithContexts K)
          ((contextTheory base spacePresentation).regionReading probeData),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : Contexts.Interface → Prop)
        (map : ContextMap (checkerWithContexts K)
          ((contextTheory base spacePresentation).regionReading declared)), ¬ map.Hosting :=
  separateProcess_checkerWithContexts_row (presentation := spacePresentation)
    probeWithSpace_quoteDropOnly probeWithSpace_separateProcess.1
    probeWithSpace_separateProcess.2.1 probeWithSpace_separateProcess.2.2.1
    probeWithSpace_separateProcess.2.2.2 step

/-- **So it hosts with contexts the checker of no MM0 theory**, under any
evaluator and any reading. -/
theorem space_mm0CheckerWithContexts_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    IsEmpty (ContextMap (mm0CheckerWithContexts T) (contextTheory base spacePresentation)) ∧
      (∀ map : ContextMap (mm0CheckerWithContexts T)
          ((contextTheory base spacePresentation).regionReading probeData),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : Contexts.Interface → Prop)
        (map : ContextMap (mm0CheckerWithContexts T)
          ((contextTheory base spacePresentation).regionReading declared)), ¬ map.Hosting := by
  obtain ⟨state, next, step⟩ := mm0Checker_has_step T
  exact space_checkerWithContexts_row base step

#print axioms probeWithSpace_separateProcess
#print axioms probeWithSpace_takes_atoms
#print axioms space_checkerWithContexts_row
#print axioms space_mm0CheckerWithContexts_row

end Mettapedia.Logic.HostingStyles.Guests
