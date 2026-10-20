import Mettapedia.Logic.MarkovLogicAbstract
import Mettapedia.PLN.Comparisons.StructuralAdvantages

/-!
# What a mass semantics cannot say about confidence

`StructuralAdvantages.strengthOnly_readout_loses_total` is a statement about an
arbitrary readout that depends only on strength.  This file discharges its
hypothesis for Markov Logic, so the comparison it was written for becomes a
theorem rather than a claim.

The bridge is already in the tree and is exact, not an analogy:

* `Mettapedia.ProbabilityTheory.MassSemantics.binaryMass q = ⟨queryMass q, totalMass - queryMass q⟩`
  is the evidence a query induces;
* `Mettapedia.ProbabilityTheory.MassSemantics.toStrength_binaryMass` proves
  `toStrength (binaryMass q) = queryProb q` — a Markov Logic query
  probability **is** the PLN strength of that evidence;
* `Mettapedia.ProbabilityTheory.MassSemantics.binaryMass_total` proves
  `(binaryMass q).total = totalMass`.

The third of these is the one nobody drew a consequence from, and it is the
whole negative result. The total does not mention `q`. So within a single mass
semantics **every query carries exactly the same total evidence**: a query
settled by three observations and a query settled by three thousand are
assigned the same confidence, because confidence is computed from the total and
the total is a property of the model, not of the query.

`binaryMass_never_oneFailure_and_twoFailures` states this in the sharpest
available form: no mass semantics induces both of
`StructuralAdvantages`'s two witnesses, which differ only in total. PLN's
representation holds both, since they are just values of `BinaryEvidence`.

The statement concerns this mass readout, not a deficiency of Markov Logic.
The finite ProbLog bridge supplies the same interface and identifies its
proposition readouts with `binaryMass`; the theorem therefore applies there
as well. It does not apply to a model augmented with query-specific
observation counts merely because that model also has query probabilities.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons

open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.PLN.Evidence

variable {Query : Type*}

/-! ## The readout is strength-determined -/

/-- **A mass semantics' query probability depends only on strength**, which is
the hypothesis of `strengthOnly_readout_loses_total`.  Immediate from the
existing bridge. -/
theorem queryProb_strengthDetermined (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q₁ q₂ : Query)
    (h : BinaryEvidence.toStrength (S.binaryMass q₁)
       = BinaryEvidence.toStrength (S.binaryMass q₂)) :
    S.queryProb q₁ = S.queryProb q₂ := by
  rw [← S.toStrength_binaryMass q₁, ← S.toStrength_binaryMass q₂]
  exact h

/-! ## And the total it is computed against does not depend on the query -/

/-- **Every query carries the same total evidence.**  Both totals are the
model's `totalMass`, which mentions no query. -/
theorem binaryMass_total_query_independent
    (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q₁ q₂ : Query) :
    (S.binaryMass q₁).total = (S.binaryMass q₂).total := by
  rw [S.binaryMass_total q₁, S.binaryMass_total q₂]

/-- **The negative structural theorem.**  No mass semantics induces both of the
two evidence states that differ only in total.  A framework of this shape
therefore cannot distinguish one failure from two. -/
theorem binaryMass_never_oneFailure_and_twoFailures
    (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q₁ q₂ : Query) :
    ¬ (S.binaryMass q₁ = oneFailure ∧ S.binaryMass q₂ = twoFailures) := by
  rintro ⟨h₁, h₂⟩
  have htot := binaryMass_total_query_independent S q₁ q₂
  rw [h₁, h₂] at htot
  exact total_separates htot

/-- Said the other way round: if two queries' induced evidence differ at all,
they differ in strength, never in total. -/
theorem binaryMass_differ_only_in_strength
    (S : Mettapedia.ProbabilityTheory.MassSemantics Query) (q₁ q₂ : Query)
    (hne : S.binaryMass q₁ ≠ S.binaryMass q₂) :
    (S.binaryMass q₁).pos ≠ (S.binaryMass q₂).pos ∧
      (S.binaryMass q₁).total = (S.binaryMass q₂).total := by
  refine ⟨?_, binaryMass_total_query_independent S q₁ q₂⟩
  intro hpos
  refine hne (BinaryEvidence.ext' hpos ?_)
  show S.totalMass - S.queryMass q₁ = S.totalMass - S.queryMass q₂
  rw [show S.queryMass q₁ = S.queryMass q₂ from hpos]

/-! ## Controls -/

namespace MarkovLogicConfidenceControls

/-- The contrast, so the theorem is not vacuous: PLN's representation *does*
hold both witnesses, because they are values of `BinaryEvidence`. -/
theorem pln_holds_both : oneFailure ≠ twoFailures := evidence_separates

/-- And they differ exactly where a mass semantics cannot: in total. -/
theorem pln_totals_differ : oneFailure.total ≠ twoFailures.total := total_separates

/-- Strength alone does not separate them, which is why a strength-determined
readout is blind to the difference. -/
theorem strengths_agree :
    BinaryEvidence.toStrength oneFailure = BinaryEvidence.toStrength twoFailures := by
  rw [oneFailure_strength, twoFailures_strength]

end MarkovLogicConfidenceControls

end Mettapedia.PLN.Comparisons

#print axioms Mettapedia.PLN.Comparisons.queryProb_strengthDetermined
#print axioms Mettapedia.PLN.Comparisons.binaryMass_total_query_independent
#print axioms Mettapedia.PLN.Comparisons.binaryMass_never_oneFailure_and_twoFailures
