import Mettapedia.SetTheory.OpenTower.AntiFounded.AFAStages

/-!
# The height map of the closed stages and its two sections

The *height* of a closed stage is the rank of its well-founded part (`height`). It is monotone
(`height_mono`), and the heights that occur are `0`, `ω` and `κ` for `κ` inaccessible
(`hclosed_classification`). Over each height there is a whole fibre of closed stages.

**Two adjoint sections.** For every height `κ` of a closed stage, `V_κ` is the least stage of
that height and `B_κ` the greatest, and both are sections of the height map
(`height_ofZFSet_vonNeumann`, `height_branching`). More precisely, `V_κ` is left adjoint and
`B_κ` right adjoint to the height map:

* `ofZFSet (V_κ) ⊆ U ↔ κ ≤ height U` (`ofZFSet_vonNeumann_subset_iff`), for every closed `U`;
* `U ⊆ B_κ ↔ height U ≤ κ` (`subset_branching_iff`), for every closed `U` and every `κ` that is
  `0`, `ℵ₀` or inaccessible.

So the height map carves the closed stages into fibres, each an interval from its least to its
greatest stage.

**Closure under anti-foundation chooses the right section.** Over each inaccessible height the
fibre of stages closed under anti-foundation is a single stage, `B_κ`
(`existsUnique_afaClosed_of_height`). So on inaccessible heights, closure under anti-foundation
is a section of the height map, and it is the right adjoint one.

**Controls.** The fibres of the plain closed stages are never singletons above `0`: `V_κ` and
`B_κ` differ (`fibre_not_subsingleton`). Over `ω` the fibre is not even a chain
(`exists_incomparable_hclosed`). The fibre over `0` is `{∅}` (`height_eq_zero_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-- The height of a hyperset: the rank of its well-founded part. -/
noncomputable def height (U : HSet.{u}) : Ordinal.{u} :=
  (HSet.toZFSet U).rank

theorem height_mono {U V : HSet.{u}} (h : U ⊆ V) : height U ≤ height V :=
  ZFSet.rank_mono (toZFSet_mono h)

/-- The well-founded part of a closed stage is the level at its height. -/
theorem HClosed.toZFSet_eq {U : HSet.{u}} (hU : HClosed U) :
    HSet.toZFSet U = V_ (height U) :=
  closed_eq_vonNeumann hU.closed_toZFSet

theorem height_ofZFSet (V : ZFSet.{u}) : height (HSet.ofZFSet V) = V.rank := by
  rw [height, HSet.toZFSet_ofZFSet]

theorem height_ofZFSet_vonNeumann (α : Ordinal.{u}) : height (HSet.ofZFSet (V_ α)) = α := by
  rw [height_ofZFSet, ZFSet.rank_vonNeumann]

theorem height_branching {κ : Cardinal.{u}} (h : HClosed (branching κ)) :
    height (branching κ) = κ.ord := by
  rw [height, toZFSet_branching h, ZFSet.rank_vonNeumann]

/-- **`V_κ` is left adjoint to the height map.** -/
theorem ofZFSet_vonNeumann_subset_iff {U : HSet.{u}} (hU : HClosed U) (α : Ordinal.{u}) :
    HSet.ofZFSet (V_ α) ⊆ U ↔ α ≤ height U := by
  constructor
  · intro h
    rw [← height_ofZFSet_vonNeumann α]
    exact height_mono h
  · intro h
    have inside : V_ α ⊆ HSet.toZFSet U := by
      rw [hU.toZFSet_eq]
      exact ZFSet.vonNeumann_subset_vonNeumann_iff.mpr h
    exact hset_subset_trans (ofZFSet_subset_ofZFSet inside) (ofZFSet_toZFSet_subset U)

/-- **`B_κ` is right adjoint to the height map.** -/
theorem subset_branching_iff {U : HSet.{u}} (hU : HClosed U) {κ : Cardinal.{u}}
    (hκ : HClosed (branching κ)) : U ⊆ branching κ ↔ height U ≤ κ.ord := by
  constructor
  · intro h
    rw [← height_branching hκ]
    exact height_mono h
  · intro h
    rcases hclosed_classification hU with rfl | ⟨μ, _, hW, _, hUμ⟩
    · exact hset_empty_subset _
    · have hμ : μ.ord ≤ κ.ord := by
        have equal : height U = μ.ord := by rw [height, hW, ZFSet.rank_vonNeumann]
        rwa [equal] at h
      exact hset_subset_trans hUμ (branching_mono (ord_le_ord.mp hμ))

/-- The fibre over `0` is `{∅}`. -/
theorem height_eq_zero_iff {U : HSet.{u}} (hU : HClosed U) : height U = 0 ↔ U = ∅ := by
  constructor
  · intro h
    have inside : U ⊆ branching 0 := by
      rw [subset_branching_iff hU (hclosed_branching_iff.mpr (Or.inl rfl)), h, ord_zero]
    rw [branching_zero] at inside
    exact HSet.eq_empty_iff.mpr fun z hz => HSet.notMem_empty z (HSet.subset_iff.mp inside hz)
  · rintro rfl
    rw [height, ← HSet.ofZFSet_empty, HSet.toZFSet_ofZFSet, ZFSet.rank_empty]

/-- **Above `0`, the fibres of the plain closed stages are not singletons.** -/
theorem fibre_not_subsingleton {κ : Cardinal.{u}} (hκ : κ = ℵ₀ ∨ κ.IsInaccessible) :
    HClosed (HSet.ofZFSet (V_ κ.ord)) ∧ HClosed (branching κ) ∧
      height (HSet.ofZFSet (V_ κ.ord)) = κ.ord ∧ height (branching κ) = κ.ord ∧
      HSet.ofZFSet (V_ κ.ord) ≠ branching κ := by
  have hB : HClosed (branching κ) := hclosed_branching_iff.mpr (Or.inr hκ)
  have hV : HClosed (HSet.ofZFSet (V_ κ.ord)) := by
    rw [← toZFSet_branching hB]
    exact hclosed_ofZFSet_iff.mpr hB.closed_toZFSet
  refine ⟨hV, hB, height_ofZFSet_vonNeumann _, height_branching hB, fun equal => ?_⟩
  have aleph : ℵ₀ ≤ κ := by
    rcases hκ with rfl | hκ
    · exact le_rfl
    · exact hκ.aleph0_lt.le
  have member : HSet.quineAtom ∈ branching κ :=
    HSet.subset_iff.mp (branching_mono aleph) quineAtom_mem_branching
  rw [← equal] at member
  exact HSet.not_wf_quineAtom ((HSet.wf_ofZFSet _).mem member)

/-- **Closure under anti-foundation is a section of the height map over the inaccessible
heights**: over each inaccessible height there is exactly one stage closed under
anti-foundation, `B_κ`. -/
theorem existsUnique_afaClosed_of_height {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    ∃! U : HSet.{u}, AFAClosed U ∧ height U = κ.ord := by
  have hB := afaClosed_branching (Or.inr hκ)
  refine ⟨branching κ, ⟨hB, height_branching hB.toHClosed⟩, fun U ⟨hU, hheight⟩ => ?_⟩
  exact hU.eq_branching hκ (by rw [hU.toHClosed.toZFSet_eq, hheight])

/-- The section `κ ↦ B_κ` over the inaccessible heights is injective and monotone. -/
theorem branching_section_strictMono {κ μ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    (hμ : μ.IsInaccessible) (h : κ < μ) :
    branching κ ⊆ branching μ ∧ branching κ ≠ branching μ := by
  refine ⟨branching_mono h.le, fun equal => ?_⟩
  have heights := height_branching (afaClosed_branching (Or.inr hκ)).toHClosed
  rw [equal, height_branching (afaClosed_branching (Or.inr hμ)).toHClosed] at heights
  exact h.ne (ord_injective heights.symm)

#print axioms ofZFSet_vonNeumann_subset_iff
#print axioms subset_branching_iff
#print axioms height_eq_zero_iff
#print axioms fibre_not_subsingleton
#print axioms existsUnique_afaClosed_of_height

end Mettapedia.SetTheory.OpenTower.AntiFounded
