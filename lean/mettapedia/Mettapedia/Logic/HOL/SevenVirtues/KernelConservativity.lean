import Mettapedia.Languages.HOLLight.RetainedElaboration
import Mettapedia.Languages.OpenTheory.EtaCompletenessHeyting

/-!
# Virtue 7: the HOL Light kernel proves nothing beyond the calculus

The theorems below were already proved in the tree; this file composes them
for the implemented checker and indexes them.

* `checker_translatedProvable`: every proof graph accepted by the HOL Light
  kernel checker without axioms has a translated conclusion derivable in the
  EM-free extensional calculus (`ExtDerivation`) from the translated
  hypotheses.  The derivation is computed: `elaborateProved` elaborates the
  graph into a retained proof (`elaborateProved_correct`), and erasure gives
  the derivation.  No countability, completeness theorem, or excluded middle
  is used.
* With the eta axiom, the OpenTheory kernel proves exactly the sequents with
  Boolean hypotheses whose translations are derivable
  (`EtaCompleteness.kernelProvable_etaAxiomPolicy_iff_translatedProvable`), and
  exactly the Heyting-valued consequences over its own signature
  (`EtaCompleteness.kernelProvable_etaAxiomPolicy_iff_heytingConsequence`).
* Negative controls: the eta sequent is translated-derivable but not provable
  without the eta axiom
  (`EtaCompletenessExamples.exists_translatedProvable_not_kernelProvable_emptyAxiomPolicy`),
  and excluded middle is not provable even with it
  (`EtaCompletenessHeytingExamples.excludedMiddle_not_kernelProvable_etaAxiomPolicy`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.KernelConservativity

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight

/-- **The kernel without axioms proves nothing beyond the calculus.**  An
accepted HOL Light proof graph has a translated conclusion that is EM-free
derivable from its translated hypotheses. -/
theorem checker_translatedProvable {claim : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim certificate = true) :
    TranslatedProvable ∅ claim.sequent := by
  obtain ⟨proved, _, translation, hypotheses⟩ :=
    RetainedElaboration.elaborateProved_correct accepted
  refine ⟨proved.1.2, translation, proved.1.1, fun ψ hψ => Or.inr (hypotheses ψ hψ), ?_⟩
  exact proved.2.erase

/-- Positive control: the reflexivity graph. -/
theorem reflexivity_translatedProvable :
    TranslatedProvable ∅ ProofExecution.Controls.reflexivityTheorem.sequent :=
  checker_translatedProvable ProofSystem.Controls.reflexivity_accepted

#check @EtaCompleteness.kernelProvable_etaAxiomPolicy_iff_translatedProvable
#check @EtaCompleteness.kernelProvable_etaAxiomPolicy_iff_heytingConsequence
#check @EtaCompletenessExamples.exists_translatedProvable_not_kernelProvable_emptyAxiomPolicy
#check @EtaCompletenessHeytingExamples.excludedMiddle_not_kernelProvable_etaAxiomPolicy

end Mettapedia.Logic.HOL.SevenVirtues.KernelConservativity
