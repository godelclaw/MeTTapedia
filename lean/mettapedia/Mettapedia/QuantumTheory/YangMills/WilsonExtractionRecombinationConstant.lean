import Mettapedia.QuantumTheory.YangMills.ExtendedExtractionTransfer
import Mettapedia.QuantumTheory.YangMills.RGBootstrapSlack
import Mettapedia.QuantumTheory.YangMills.WilsonPolymerRecombination

/-!
# The v14 extraction/recombination constant: arithmetic verdict

This module separates three quantities that had been conflated.

1. The displayed F.5 product, read with `7.4 = 37/5`, is `33152` at block
   factor two, not `2224`.
2. Appendix O's different proposed ledger gives `11088/5` when its extraction
   factor is `2`, and `5544/5` when our Wilson-coordinate majorant extraction
   factor `1` is used.  These are conditional ledger calculations: the other
   fluctuation, cumulant-generation, and rooted tree-graph factors have not been
   proved for the actual Wilson RG map.
3. The manuscript's stated data cannot derive either advertised component:
   a range-only projection need not have norm at most two, and two lattice
   polymers can have more than fourteen contact edges.  These are explicit
   countermodels, not merely missing definitions.

Thus there is no presently derived `C_true` for the v14 Wilson RG recursion.
The natural majorant realization does decide the extraction component (`1`),
and exact regrouping by union decides the recombination-operator component
(`1`); the remaining constant belongs to the prior analytic map producing
connected cumulant families.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## The two inconsistent manuscript ledgers -/

/-- F.5's displayed factor product at `b = 2`, interpreting decimal `7.4`
exactly as `37/5`. -/
def f5DisplayedConstantAtBlockTwo : ℝ :=
  ((37 : ℝ) / 5) * 10 * (2 : ℝ) ^ 4 * 14 * 2

theorem f5DisplayedConstantAtBlockTwo_eq :
    f5DisplayedConstantAtBlockTwo = 33152 := by
  norm_num [f5DisplayedConstantAtBlockTwo]

/-- The unexplained division by fifteen in F.5 cannot turn its displayed
factor product into the advertised constant. -/
theorem f5DisplayedConstantAtBlockTwo_ne_2224 :
    f5DisplayedConstantAtBlockTwo ≠ 2224 := by
  rw [f5DisplayedConstantAtBlockTwo_eq]
  norm_num

/-- Appendix O's alternative proposed factor ledger at `b = 2`, parameterized
by the extraction norm.  The adjective "proposed" is load-bearing: this
definition does not assert the other analytic factors for the Wilson RG map. -/
def appendixOProposedConstantAtBlockTwo (Cextract : ℝ) : ℝ :=
  ((33 : ℝ) / 20) * (3 * (2 : ℝ) ^ 4) * 14 * Cextract

theorem appendixOProposedConstantAtBlockTwo_extraction_two_eq :
    appendixOProposedConstantAtBlockTwo 2 = (11088 : ℝ) / 5 := by
  norm_num [appendixOProposedConstantAtBlockTwo]

theorem appendixOProposedConstantAtBlockTwo_extraction_two_lt_2224 :
    appendixOProposedConstantAtBlockTwo 2 < 2224 := by
  rw [appendixOProposedConstantAtBlockTwo_extraction_two_eq]
  norm_num

/-- Proposed Appendix-O ledger after substituting the proved norm-one
Wilson-coordinate majorant extraction component. -/
def proposedMajorantLedgerConstant : ℝ :=
  appendixOProposedConstantAtBlockTwo 1

theorem proposedMajorantLedgerConstant_eq :
    proposedMajorantLedgerConstant = (5544 : ℝ) / 5 := by
  norm_num [proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo]

/-! ## Bootstrap consequence of the proposed majorant ledger -/

theorem proposedMajorantLedger_rgGain_two_fifteen_eq :
    rgGain proposedMajorantLedgerConstant 2 15 = (693 : ℝ) / 2560 := by
  norm_num [rgGain, proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo, irrelevantScale]

theorem proposedMajorantLedger_rgGain_two_fourteen_eq :
    rgGain proposedMajorantLedgerConstant 2 14 = (693 : ℝ) / 1280 := by
  norm_num [rgGain, proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo, irrelevantScale]

/-- If the other Appendix-O factors were proved unchanged in the majorant
norm, depth `15` would already meet the stronger two-source `1/3` budget. -/
theorem proposedMajorantLedger_twoSourceSlack_two_fifteen :
    HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 15 := by
  refine ⟨?_, ?_⟩
  · norm_num [proposedMajorantLedgerConstant,
      appendixOProposedConstantAtBlockTwo]
  · rw [proposedMajorantLedger_rgGain_two_fifteen_eq]
    norm_num

/-- Under that same proposed ledger, no depth at most `14` meets the two-source
budget. -/
theorem not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen
    {D : ℕ} (hD : D ≤ 14) :
    ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D := by
  intro h
  have hg := h.2
  interval_cases D <;>
    norm_num [rgGain, proposedMajorantLedgerConstant,
      appendixOProposedConstantAtBlockTwo, irrelevantScale] at hg

/-- Conditional depth verdict: `15` is the least unrestricted depth for the
proposed majorant ledger.  If the extracted action sector is restricted to
even canonical dimensions, the least admissible depth remains `16`. -/
theorem proposedMajorantLedger_leastDepth_and_leastEvenDepth :
    (HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 15 ∧
      ∀ D, D ≤ 14 →
        ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D) ∧
    (HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 16 ∧
      ∀ D, Even D → D < 16 →
        ¬ HasTwoSourceBootstrapSlack proposedMajorantLedgerConstant 2 D) := by
  refine ⟨⟨proposedMajorantLedger_twoSourceSlack_two_fifteen,
      fun _ hD => not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen hD⟩,
    ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · norm_num [proposedMajorantLedgerConstant,
        appendixOProposedConstantAtBlockTwo]
    · norm_num [rgGain, proposedMajorantLedgerConstant,
        appendixOProposedConstantAtBlockTwo, irrelevantScale]
  · intro D hEven hD
    rcases hEven with ⟨k, hk⟩
    exact not_proposedMajorantLedger_twoSourceSlack_of_depth_le_fourteen
      (by omega)

/-! ## Machine-checked impossibility of the literal v14 component package -/

/-- The two load-bearing literal universal readings of the v14 component
claims: every algebraic low-space projection has bound two, and every pair of
lattice polymers has at most fourteen contacts. -/
def V14LiteralExtractionRecombinationClaims : Prop :=
  (∀ P : (ℝ × ℝ) → (ℝ × ℝ),
      IsProjectionOntoFirstCoordinate P →
      ∀ x, pairL1 (P x) ≤ 2 * pairL1 x) ∧
    polymerContactCount contactStripLeft contactStripRight ≤ 14

/-- **Final as-written verdict.**  The literal component package required to
derive the advertised v14 constant is false.  Both conjuncts have independent
explicit counterexamples in the imported modules. -/
theorem not_v14LiteralExtractionRecombinationClaims :
    ¬ V14LiteralExtractionRecombinationClaims := by
  intro h
  have hcontacts := h.2
  exact (Nat.not_lt_of_ge hcontacts) fourteen_lt_contactStrip_rail_contacts

end YangMills
end QuantumTheory
end Mettapedia
