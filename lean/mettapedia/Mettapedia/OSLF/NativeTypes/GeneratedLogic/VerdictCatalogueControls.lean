import Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogue
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls

/-!
# Controls: the verdict catalogue

- **Proofs carry over.** A checking proof is an established verdict; an admission refusal makes no claim
  (`checking_proof`, `admission_refusal`).
- **The OSLF checker proves a generated formula.** It answers `sat` for "a box around the empty bag" at
  `Box({})`. Read through the catalogue, that answer is a proof that the generated formula the OSLF
  formula embeds as holds there (`checker_establishes`, `checker_proves_generated`).
- **A failed check makes no claim.** At `Box({A})` the checker does not answer `sat`, and the verdict is
  suspended rather than refuted (`checker_silent`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogueControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Verdicts
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings (syntactic ofOSLF)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.EmbeddingControls (atomFree atomFails noAtoms noAtoms_agree noStep boxedEmpty atomA)

theorem checking_proof :
    (ofChecking (.proof trivial : Mettapedia.OSLF.NativeTypes.Semantics.Checking.Verdict True)).answer = some true :=
  rfl

theorem admission_refusal (reason : Mettapedia.OSLF.NativeTypes.Decision.Admission.Refusal) :
    (ofAdmission (.refused reason : Mettapedia.OSLF.NativeTypes.Decision.Admission.Verdict False)).answer = none :=
  rfl

/-- No steps, listed. -/
def noSteps : Pattern → List Pattern := fun _ => []

theorem noSteps_sound : ∀ pattern next, next ∈ noSteps pattern → noStep pattern next := by
  intro _ _ member
  simp [noSteps] at member

/-- The checker's verdict about the generated formula, at a term. -/
def boxVerdict (term : Pattern) :=
  ofOSLFCheckGenerated (positive := atomFree) (negative := atomFails) (relation := noStep) (step := noSteps)
    (atomCheck := fun _ _ => false) (atoms := fun _ _ => False) (fun _ _ never => absurd never Bool.false_ne_true)
    noSteps_sound 4 term boxedEmpty (by decide) (by decide) noAtoms_agree

theorem checker_establishes : (boxVerdict (.apply "Box" [.collection .hashBag [] none])).answer = some true := by
  decide +kernel

/-- **The OSLF checker proves the generated formula.** -/
theorem checker_proves_generated :
    (syntactic noStep).sat noAtoms (ofOSLF atomFree atomFails 0 true boxedEmpty) (.apply "Box" [.collection .hashBag [] none]) :=
  Verdict.holds_of_answer checker_establishes

/-- **A failed check is silent.** -/
theorem checker_silent : (boxVerdict (.apply "Box" [.collection .hashBag [atomA] none])).answer = none := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.VerdictCatalogueControls
