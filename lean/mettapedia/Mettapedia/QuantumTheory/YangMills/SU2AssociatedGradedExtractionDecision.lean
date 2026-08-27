import Mettapedia.QuantumTheory.YangMills.SU2AssociatedGradedExtraction
import Mettapedia.QuantumTheory.YangMills.SU2IndependentTraceBasis
import Mettapedia.QuantumTheory.YangMills.Dimension16WilsonExtractionCertificate
import Mettapedia.QuantumTheory.YangMills.WilsonExtractionRecombinationConstant
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Constant decision for the associated-graded `SU(2)` extraction

This module feeds the literal manuscript-supremum-norm extraction constant
proved by `SU2AssociatedGradedExtraction` into the existing Appendix-O ledger
arithmetic.  The fluctuation, connected-cumulant, and recombination numbers in
that ledger remain the manuscript's proposed factors; this file does not prove
them for the Wilson RG map.

The associated-graded extraction factor on the actual gauge-fixed block chart
is

`C_extract = 131071 / 65536 < 2`.

With the other proposed Appendix-O factors left unchanged, the resulting
conditional recursion constant is `90832203 / 40960 < 2224`, and depth sixteen
still meets the stronger two-source `1/3` bootstrap budget.  This is a positive
decision for our associated-graded extraction construction, not a derivation
of v14's unenumerated continuum `F,D` quotient or of the full Yang--Mills
recursion.  The exact one-plaquette Cayley--Hamilton trace quotient also has an
independent-basis extractor with factor `31/16 < 2`; it is kept as a scoped
positive result rather than silently promoted to the full block quotient.

The transfer audit is decisive about scope.  Our associated-graded space has
dimension `12875774670`, so it cannot be linearly equivalent to any coordinate
space of dimension at most v14's asserted bound `1851`.  A nontrivial quotient
or invariant projection is required.  V14 does not define one coherently:
F.4 uses an on-shell EOM policy while O.9 explicitly retains EOM operators.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace SU2AssociatedGradedExtractionDecision

open SU2AssociatedGradedExtraction
open SU2IndependentTraceBasis

/-- Appendix-O's proposed ledger with the proved associated-graded extraction
factor substituted and every other proposed factor unchanged. -/
def associatedGradedProposedLedgerConstant : ℝ :=
  appendixOProposedConstantAtBlockTwo manuscriptSupExtractionConstant16

theorem associatedGradedProposedLedgerConstant_eq :
    associatedGradedProposedLedgerConstant = (90832203 : ℝ) / 40960 := by
  norm_num [associatedGradedProposedLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    manuscriptSupExtractionConstant16]

theorem associatedGradedProposedLedgerConstant_lt_2224 :
    associatedGradedProposedLedgerConstant < 2224 := by
  rw [associatedGradedProposedLedgerConstant_eq]
  norm_num

theorem associatedGradedProposedLedger_rgGain_two_sixteen_eq :
    rgGain associatedGradedProposedLedgerConstant 2 16 =
      (90832203 : ℝ) / 335544320 := by
  norm_num [rgGain, associatedGradedProposedLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    manuscriptSupExtractionConstant16, irrelevantScale]

/-- Conditional arithmetic consequence: if the three unchanged Appendix-O
factors are actually proved in the same supremum norm, our associated-graded
extraction keeps depth sixteen inside the two-source `1/3` budget. -/
theorem associatedGradedProposedLedger_twoSourceSlack_two_sixteen :
    HasTwoSourceBootstrapSlack
      associatedGradedProposedLedgerConstant 2 16 := by
  constructor
  · rw [associatedGradedProposedLedgerConstant_eq]
    norm_num
  · rw [associatedGradedProposedLedger_rgGain_two_sixteen_eq]
    norm_num

/-- Depth fifteen still misses the stronger two-source budget under this
conditional ledger. -/
theorem not_associatedGradedProposedLedger_twoSourceSlack_two_fifteen :
    ¬ HasTwoSourceBootstrapSlack
      associatedGradedProposedLedgerConstant 2 15 := by
  intro h
  have hg := h.2
  norm_num [rgGain, associatedGradedProposedLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    manuscriptSupExtractionConstant16, irrelevantScale] at hg

/-- The exact associated-graded monomial census is far larger than the
unsupported `1851` bound in v14.  The two spaces must not be identified: ours
is the full gauge-fixed jet space, while v14 describes a smaller continuum
gauge-invariant operator quotient without enumerating it. -/
theorem manuscriptOperatorCount_not_ourJetCount :
    1851 < Fintype.card BlockJetMonomial16 := by
  rw [blockJetMonomial16_card]
  norm_num

/-- Exact finite dimension of our full gauge-fixed associated-graded block
space. -/
theorem blockAssociatedGraded16_finrank :
    Module.finrank ℂ BlockAssociatedGraded16 = 12875774670 := by
  rw [Module.finrank_eq_card_basis blockAssociatedGradedBasis16,
    blockJetMonomial16_card]

/-- **Concrete transfer obstruction.**  The full associated-graded block
space cannot be identified by a linear equivalence with any coordinate space
of dimension at most the manuscript's asserted `1851` bound.  A separately
constructed invariant quotient/projection is mathematically necessary. -/
theorem no_associatedGraded_linearEquiv_atMost1851
    {n : ℕ} (hn : n ≤ 1851) :
    ¬ Nonempty (BlockAssociatedGraded16 ≃ₗ[ℂ] (Fin n → ℂ)) := by
  rintro ⟨e⟩
  have hfinrank := LinearEquiv.finrank_eq e
  rw [blockAssociatedGraded16_finrank,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfinrank
  omega

/-! ## Exhaustive survivor/transfer audit -/

inductive ExtractionDecisionRow where
  | independentTraceQuotient
  | independentFullV14Transfer
  | associatedGradedBlockChart
  | associatedFullV14Transfer
  | associatedLiteralSupNorm
  | appendixOLedger
deriving DecidableEq, Fintype, Repr

inductive ExtractionDecisionStatus where
  | constructed
  | transferObstructed
  | sourcePolicyConflict
  | conditionalOnUnchangedFactors
deriving DecidableEq, Repr

/-- Checked outcome matrix.  `constructed` means a theorem on the named
object, never transfer by analogy. -/
def extractionDecisionStatus :
    ExtractionDecisionRow → ExtractionDecisionStatus
  | .independentTraceQuotient => .constructed
  | .independentFullV14Transfer => .sourcePolicyConflict
  | .associatedGradedBlockChart => .constructed
  | .associatedFullV14Transfer => .transferObstructed
  | .associatedLiteralSupNorm => .constructed
  | .appendixOLedger => .conditionalOnUnchangedFactors

def extractionDecisionMatrix :
    List (ExtractionDecisionRow × ExtractionDecisionStatus) :=
  [ (.independentTraceQuotient, .constructed)
  , (.independentFullV14Transfer, .sourcePolicyConflict)
  , (.associatedGradedBlockChart, .constructed)
  , (.associatedFullV14Transfer, .transferObstructed)
  , (.associatedLiteralSupNorm, .constructed)
  , (.appendixOLedger, .conditionalOnUnchangedFactors)
  ]

theorem extractionDecisionRow_count :
    Fintype.card ExtractionDecisionRow = 6 := by decide

theorem extractionDecisionMatrix_length :
    extractionDecisionMatrix.length = 6 := by decide

theorem extractionDecisionMatrix_agrees
    (row : ExtractionDecisionRow) :
    (row, extractionDecisionStatus row) ∈ extractionDecisionMatrix := by
  cases row <;> decide

/-- Checked decision payload.  Its first four fields are unconditional
mechanical theorems; the final field is explicitly the conditional Appendix-O
arithmetic with the other proposed factors unchanged. -/
structure AssociatedGradedExtractionDecisionSeal : Prop where
  exactBlockCoordinates : Fintype.card BlockLogCoordinate = 21
  exactJetCount : Fintype.card BlockJetMonomial16 = 12875774670
  jetMatrixIdentity : blockJetMatrix16 = 1
  extractionStrictlyBelowTwo : manuscriptSupExtractionConstant16 < 2
  independentTraceExtractionStrictlyBelowTwo :
    independentTraceSupExtractionConstant16 < 2
  associatedSpaceNotThe1851Space :
    ¬ Nonempty (BlockAssociatedGraded16 ≃ₗ[ℂ] (Fin 1851 → ℂ))
  sourcePoliciesConflict :
    v14F4RelationPolicy ≠ v14O9RelationPolicy
  conditionalDepthSixteen :
    HasTwoSourceBootstrapSlack
      associatedGradedProposedLedgerConstant 2 16

theorem associatedGradedExtractionDecision_sealed :
    AssociatedGradedExtractionDecisionSeal := by
  exact
    ⟨blockLogCoordinate_card,
      blockJetMonomial16_card,
      blockJetMatrix16_eq_one,
      manuscriptSupExtractionConstant16_lt_two,
      independentTraceSupExtractionConstant16_lt_two,
      no_associatedGraded_linearEquiv_atMost1851 (by rfl),
      v14F4RelationPolicy_ne_v14O9RelationPolicy,
      associatedGradedProposedLedger_twoSourceSlack_two_sixteen⟩

end SU2AssociatedGradedExtractionDecision
end YangMills
end QuantumTheory
end Mettapedia
