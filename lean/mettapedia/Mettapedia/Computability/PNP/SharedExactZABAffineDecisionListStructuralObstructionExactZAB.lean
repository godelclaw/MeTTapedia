import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListCharacterization
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionRawBitVec
import Mettapedia.Computability.PNP.SharedExactZABAffineFeatureSharpness
import Mathlib.Tactic.NormNum

/-!
# P vs NP crux: exact-ZAB transport for shared affine decision-list obstruction

The raw `BitVec` first-active affine-signature obstruction is transported
through the canonical exact-ZAB visible-data bijection for identity extractors.
-/

namespace Mettapedia.Computability.PNP

section ExactZAB

theorem bitVecZABVisibleData_bijective {n k : ℕ} :
    Function.Bijective (bitVecZABVisibleData (r := n) (k := k)) := by
  refine (Fintype.bijective_iff_injective_and_card
    (bitVecZABVisibleData (r := n) (k := k))).2 ?_
  refine ⟨bitVecZABVisibleData_injective (n := n) (k := k), ?_⟩
  rw [card_exactVisiblePostSwitchSurface_bitVec, card_bitVecZABVisibleSurface]

theorem not_injective_exactZABAffineDecisionListSignature_id_of_one_lt
    {n p k : ℕ}
    (features : Fin p → AffineColumnCode (n + (k + k)))
    (hwidth : 1 < n + (k + k)) :
    ¬ Function.Injective
      (exactZABAffineDecisionListSignature
        (Z := BitVec n) (p := p) (r := n) (k := k)
        (fun z => z) features) := by
  let g : BitVec (n + (k + k)) → Option (Fin p) :=
    fun x => firstActiveFeature? (affineFeatureVector features x)
  have hginj :
      ¬ Function.Injective g :=
    not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
      (features := features) hwidth
  have hsurj :
      Function.Surjective (bitVecZABVisibleData (r := n) (k := k)) :=
    (bitVecZABVisibleData_bijective (n := n) (k := k)).2
  intro hinj
  apply hginj
  intro x y hxy
  rcases hsurj x with ⟨u, rfl⟩
  rcases hsurj y with ⟨v, rfl⟩
  have huv : u = v := by
    apply hinj
    simpa [g, exactZABAffineDecisionListSignature, exactZABAffineFeatureSummary] using hxy
  simp [huv]

theorem fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_id_of_one_lt
    {n p k : ℕ}
    (features : Fin p → AffineColumnCode (n + (k + k)))
    (hwidth : 1 < n + (k + k)) :
    ¬ RealizedBySharedExactZABAffineDecisionListFamily
        (Z := BitVec n) (p := p) (r := n) (k := k)
        (fun z => z) features
        (fullExactVisibleRuleFamily (BitVec n) k) := by
  exact
    fullExactVisibleRuleFamily_not_realizedBySharedExactZABAffineDecisionListFamily_of_not_injective_signature
      (Z := BitVec n) (p := p) (r := n) (k := k)
      (fun z => z) features
      (not_injective_exactZABAffineDecisionListSignature_id_of_one_lt
        (p := p) (k := k) features hwidth)

end ExactZAB

end Mettapedia.Computability.PNP
