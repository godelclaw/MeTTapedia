import Mettapedia.Logic.HostingStyles.Guests.MM0Derivations
import Mettapedia.Logic.HostingStyles.Guests.MM0Checker

/-!
# MM0 as a guest of the candidate presentation: one table

The candidate is the presented probe under an evaluator `base` of its
premises, in its three readings: linear (`presentedReading base`), with
regions (`regionProbe base`), cartesian (`cartesianProbe base`).  The guest is
MM0 at three strengths.  Every cell holds for every MM0 theory `T` and every
evaluator.

| MM0 | linear | regions | cartesian |
|---|---|---|---|
| the derivations of a judgment, on terms | hosted, as numerals: `numeralsMap_hosting` | hosted, node by node: `atomsMap_hosting` on terms | hosted: `cartesianAtomsMap_hosting` on terms |
| the theory with all its derived rules | no map at all: `presented_isEmpty_contextMap_mm0ProofSystem` | hosted: `atomsMap_hosting` | hosted: `cartesianAtomsMap_hosting` |
| the checker as it runs, on terms | not hosted: `mm0Checker_not_hostedBy_row` | not hosted | not hosted |
| the checker with its contexts | no map at all | no map preserves its steps | no hosting map: `mm0CheckerWithContexts_row` |

The first three rows are `mm0_table`, one theorem; for the classes of all
theories they are `mm0_class_table`.

* Rows one and two: `T` is a proof system, kept as data.  The data that stand
  for derivations of `context ⊢ expression` exist exactly when the MM0 kernel
  derives the judgment (`exists_standsFor_iff_derives`).
* Row three: the witness is a certificate of five nodes that every theory
  accepts; its check takes five steps and the candidate has three
  (`witness_steps`).
* Row four does not depend on the length of the runs of the candidate, and it
  holds also for the candidate with a run constructor under every evaluator
  (`mm0CheckerWithContexts_run_row`).

Two sentences for a candidate that computes: with one step for each step of
the check, `HostOf candidate MM0Checker .terms .hosting`; with a nonempty
reduction for each, `RunsMM0Checkers candidate`.  What they buy:
`derives_iff_reaches_of_hostOf`, `mm0_runsCheck_reaches_iff_derives`.  The
candidate meets neither (`mm0Checker_class_row`, `not_runsMM0Checkers_row`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Presentation.Calculus
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings

/-- **Row one**: the derivations of a judgment of an MM0 theory are hosted on
terms under each of the three readings. -/
theorem mm0_derivations_row (base : BasePremiseEvaluator) (T : Kernel.Theory) (goal : Pattern) :
    (numeralsMap (mm0 T) base goal).Hosting ∧
      ((atomsMap (mm0 T) base).onTerms goal).Hosting ∧
        ((cartesianAtomsMap (mm0 T) base).onTerms goal).Hosting :=
  ⟨numeralsMap_hosting (mm0 T) base goal, (atomsMap_hosting (mm0 T) base).onTerms goal,
    (cartesianAtomsMap_hosting (mm0 T) base).onTerms goal⟩

/-- **Row two**: an MM0 theory with all its derived rules receives no map
into the linear reading and is hosted under the reading with regions and
under the cartesian reading. -/
theorem mm0_derivedRules_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    IsEmpty (ContextMap (mm0ProofSystem T) (presentedReading base)) ∧
      (atomsMap (mm0 T) base).Hosting ∧ (cartesianAtomsMap (mm0 T) base).Hosting :=
  ⟨presented_isEmpty_contextMap_mm0ProofSystem base T, atomsMap_hosting (mm0 T) base,
    cartesianAtomsMap_hosting (mm0 T) base⟩

/-- **The table**: for every MM0 theory, every judgment and every evaluator
of the premises of the candidate, the nine cells. -/
theorem mm0_table (base : BasePremiseEvaluator) (T : Kernel.Theory) (goal : Pattern) :
    ((numeralsMap (mm0 T) base goal).Hosting ∧
        ((atomsMap (mm0 T) base).onTerms goal).Hosting ∧
          ((cartesianAtomsMap (mm0 T) base).onTerms goal).Hosting) ∧
      (IsEmpty (ContextMap (mm0ProofSystem T) (presentedReading base)) ∧
        (atomsMap (mm0 T) base).Hosting ∧ (cartesianAtomsMap (mm0 T) base).Hosting) ∧
      (¬ HostedBy (mm0Checker T) (presentedReading base) ∧
        ¬ HostedBy (mm0Checker T) (regionProbe base) ∧
          ¬ HostedBy (mm0Checker T) (cartesianProbe base)) :=
  ⟨mm0_derivations_row base T goal, mm0_derivedRules_row base T,
    mm0Checker_not_hostedBy_row base T⟩

/-- **The table, for the classes**: the proof systems of all MM0 theories on
terms and with all contexts, and the checkers of all MM0 theories. -/
theorem mm0_class_table (base : BasePremiseEvaluator) :
    (HostOf (presentedReading base) MM0ProofSystem .terms .hosting ∧
        HostOf (regionProbe base) MM0ProofSystem .terms .hosting ∧
          HostOf (cartesianProbe base) MM0ProofSystem .terms .hosting) ∧
      (¬ HostOf (presentedReading base) MM0ProofSystem .contexts .hosting ∧
        HostOf (regionProbe base) MM0ProofSystem .contexts .hosting ∧
          HostOf (cartesianProbe base) MM0ProofSystem .contexts .hosting) ∧
      (¬ HostOf (presentedReading base) MM0Checker .terms .hosting ∧
        ¬ HostOf (regionProbe base) MM0Checker .terms .hosting ∧
          ¬ HostOf (cartesianProbe base) MM0Checker .terms .hosting) :=
  ⟨mm0ProofSystems_terms_row base, mm0ProofSystems_separate_readings base,
    mm0Checker_class_row base⟩

#print axioms mm0_derivations_row
#print axioms mm0_derivedRules_row
#print axioms mm0_table
#print axioms mm0_class_table

end Mettapedia.Logic.HostingStyles.Guests
