import Mettapedia.Computability.PNP.ClockedKpolyActualGapClosure
import Mettapedia.Computability.PNP.BadCodeAgreementObstruction


/-!
# PNP `Kpoly` actual-local exact-ZAB anchors

Concrete exact-ZAB ERM payload, bad-code recovery, and bare exact-visible interface boundaries for the `Kpoly` bridge.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: the concrete exact `(zfeat(z), a, b)`
decision-list ERM family closes the bundled clocked finite-learning payload at
the explicit decision-list budget. -/
theorem kpolyCoverage_anchor_exactZABDecisionListERMClockedKpolyFiniteLearningPayload
    {Z : Type*} [Fintype Z] {r k clock : ℕ} {Index : Type*}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock :=
  exactZABDecisionListERMClockedKpolyFiniteLearningPayload zfeat samples

/-- Route-coverage anchor: the bit-vector exact ZAB ERM specialization closes
the bundled clocked finite-learning payload at the explicit decision-list
budget. -/
theorem kpolyCoverage_anchor_bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
    {r k clock : ℕ} {Index : Type*} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock :=
  bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload samples

/-- Route-coverage anchor: equality with the concrete bit-vector exact ZAB ERM
family is a sufficient missing assumption for transferring the payload to a
manuscript-facing family variable. -/
theorem kpolyCoverage_anchor_clockedPayload_of_eq_bitVecZABDecisionListERMFamily
    {r k clock : ℕ} {Index : Type*} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock :=
  clockedKpolyFiniteLearningPayload_of_eq_bitVecZABDecisionListERMFamily samples hG

/-- Route-coverage anchor: exact-ZAB recovery with a bad-code agreement bound
localizes the obligation to every finite region whose sampling mass exceeds the
advertised threshold. -/
theorem kpolyCoverage_anchor_exactZABERMRecoveryData_exists_pos_mass_disagreement_in_region_of_badCode
    {Z : Type*} [Fintype Z] {r k : ℕ} {Index : Type*}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABERMRecoveryData
        (Z := Z) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index)
    (c :
      (rawExactZABDecisionListBitFamily Z r k zfeat).toEncodedFamily.BadCodes
        (G.predict i))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x)) :
    ∃ x, x ∈ region ∧ μ x ≠ 0 ∧
      (rawExactZABDecisionListBitFamily Z r k zfeat).decode c.1 x ≠
        G.predict i x :=
  h.exists_pos_mass_disagreement_in_region_of_badCode i c region hmass

/-- Route-coverage anchor: the bare exact-visible interface is insufficient for
the clocked payload below the full exact-visible surface threshold. -/
theorem kpolyCoverage_anchor_currentExactVisibleInterface_not_forall_clockedPayload_of_lt_surfaceCard
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) :=
  currentExactVisibleInterface_not_forall_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP
