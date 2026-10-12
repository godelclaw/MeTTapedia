import Mettapedia.SetTheory.Hyperuniverse.Capabilities
import Mettapedia.SetTheory.Hyperuniverse.Continuum
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Dependent sums of codes and the continuum hypothesis

Dependent-sum closure at the one level of the closed-set limit holds if and
only if the continuum is the first uncountable cardinal. A code names a closed
set, so an arbitrary subset is equinumerous with the members of a code only
when every subset of the carrier is finite, countably infinite, or of size
the continuum. In the other direction every dependent sum of member types
injects into a product of two copies of the carrier.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Classical Set
open Mettapedia.TypeTheory.TarskiUniverseCapabilities

/-! ## Selecting a Quine atom on an arbitrary subset -/

/-- The Quine atom over a chosen subset, and the empty code off it. -/
noncomputable def charFamily (S : Set N) (z : {w : N // member w univSet}) : N :=
  if z.1 ∈ S then quine else emptySet

theorem charFamily_of_mem {S : Set N} {z : {w : N // member w univSet}} (hz : z.1 ∈ S) :
    charFamily S z = quine := if_pos hz

theorem charFamily_of_not_mem {S : Set N} {z : {w : N // member w univSet}}
    (hz : z.1 ∉ S) : charFamily S z = emptySet := if_neg hz

example : charFamily univ ⟨emptySet, member_univ emptySet⟩ = quine := by
  simp [charFamily]

example : charFamily ∅ ⟨emptySet, member_univ emptySet⟩ = emptySet := by
  simp [charFamily]

/-- Dependent sum of the selected codes over the universal set. -/
abbrev charSigma (S : Set N) :=
  Σ arg : {w : N // member w univSet}, {y : N // member y (charFamily S arg)}

theorem charSigma_mem (S : Set N) (p : charSigma S) : p.1.1 ∈ S := by
  rcases p with ⟨arg, ⟨y, hy⟩⟩
  by_cases h : arg.1 ∈ S
  · exact h
  · have hB : charFamily S arg = emptySet := charFamily_of_not_mem h
    exact (member_empty y (hB ▸ hy)).elim

noncomputable def charSigmaInv (S : Set N) (z : S) : charSigma S :=
  ⟨⟨z.1, member_univ z.1⟩,
    ⟨quine, by
      let arg : {w : N // member w univSet} := ⟨z.1, member_univ z.1⟩
      have hz : arg.1 ∈ S := z.2
      exact (charFamily_of_mem (z := arg) hz).symm ▸ (member_quine quine).2 rfl⟩⟩

/-- Membership proofs do not distinguish dependent sums of member types. -/
theorem depSum_ext {a : N} {B : {x : N // member x a} → N}
    {p q : Σ arg : {x : N // member x a}, {y : N // member y (B arg)}}
    (hbase : p.1.1 = q.1.1) (hfiber : p.2.1 = q.2.1) : p = q := by
  rcases p with ⟨⟨px, hpx⟩, ⟨py, _⟩⟩
  rcases q with ⟨⟨qx, hqx⟩, ⟨qy, _⟩⟩
  cases hbase
  cases hfiber
  refine Sigma.ext (Subtype.ext rfl) ?_
  have hcode : B ⟨px, hpx⟩ = B ⟨px, hqx⟩ := congrArg B (Subtype.ext rfl)
  have hpred : ∀ z : N, member z (B ⟨px, hpx⟩) ↔ member z (B ⟨px, hqx⟩) := by
    intro z
    rw [hcode]
  exact (Subtype.heq_iff_coe_eq hpred).2 rfl

/-- The selected dependent sum is equinumerous with the chosen subset. -/
noncomputable def charSigmaEquiv (S : Set N) : charSigma S ≃ S where
  toFun p := ⟨p.1.1, charSigma_mem S p⟩
  invFun := charSigmaInv S
  left_inv := by
    rintro ⟨arg, ⟨y, hy⟩⟩
    refine depSum_ext ?_ ?_
    · rfl
    · have hmem : arg.1 ∈ S := charSigma_mem S ⟨arg, ⟨y, hy⟩⟩
      have hB : charFamily S arg = quine := charFamily_of_mem hmem
      simpa [charSigmaInv] using ((member_quine y).1 (hB ▸ hy)).symm
  right_inv z := Subtype.ext rfl

/-! ## Closure is the continuum hypothesis -/

/-- Dependent-sum closure at the one level is equivalent to the continuum
being the first uncountable cardinal. -/
theorem sigmaClosedAt_iff_continuum_eq_aleph_one :
    setCode.SigmaClosedAt PUnit.unit ↔
      Cardinal.continuum.{0} = Cardinal.aleph 1 := by
  constructor
  · intro hsig
    unfold TarskiCodeFamily.SigmaClosedAt at hsig
    have hAlephLe : Cardinal.aleph 1 ≤ Cardinal.mk N := by
      rw [mk_carrier]
      exact Cardinal.aleph_one_le_continuum
    have hSub : Cardinal.aleph 1 ≤ Cardinal.mk (univ : Set N) := by
      rw [Cardinal.mk_univ]
      exact hAlephLe
    obtain ⟨S, _, hcard⟩ := Cardinal.le_mk_iff_exists_subset.mp hSub
    obtain ⟨sum, ⟨eSum⟩⟩ := hsig univSet (charFamily S)
    have eMembers : {z : N // member z sum} ≃ S := eSum.trans (charSigmaEquiv S)
    have hClosed : IsClosed (fixedHomeo sum : Set N) := (fixedHomeo sum).isCompact'.isClosed
    have hmk : Cardinal.mk (fixedHomeo sum : Set N) = Cardinal.aleph 1 := by
      have hsame :
          Cardinal.mk (fixedHomeo sum : Set N) = Cardinal.mk {z : N // member z sum} := rfl
      rw [hsame, Cardinal.mk_congr eMembers, hcard]
    have hnot : ¬ Cardinal.mk (fixedHomeo sum : Set N) ≤ Cardinal.aleph0 := by
      rw [hmk]
      exact not_le_of_gt Cardinal.aleph0_lt_aleph_one
    rcases closed_carrier_trichotomy hClosed with hfin | ⟨hcount, _⟩ | hcont
    · have : Finite (fixedHomeo sum : Set N) := hfin
      exact absurd (Cardinal.mk_le_aleph0_iff.mpr inferInstance) hnot
    · exact absurd (Cardinal.mk_le_aleph0_iff.mpr hcount) hnot
    · exact hcont.symm.trans hmk
  · intro hCH
    unfold TarskiCodeFamily.SigmaClosedAt
    intro domain codomain
    let sigmaType :=
      Σ arg : {x : N // member x domain}, {y : N // member y (codomain arg)}
    have hinj : Function.Injective (fun p : sigmaType => (p.1.1, p.2.1)) := by
      intro p q hpq
      exact depSum_ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)
    have hle : Cardinal.mk sigmaType ≤ Cardinal.continuum.{0} :=
      (Cardinal.mk_le_of_injective hinj).trans (le_of_eq mk_prod_carrier)
    have hle1 : Cardinal.mk sigmaType ≤ Cardinal.aleph 1 := by
      rwa [hCH] at hle
    rcases le_iff_lt_or_eq.mp hle1 with hlt | heq
    · exact exists_code_of_card (Or.inl (Cardinal.lt_aleph_one_iff.mp hlt))
    · exact exists_code_of_card (Or.inr (heq.trans hCH.symm))

end Mettapedia.SetTheory.Hyperuniverse
