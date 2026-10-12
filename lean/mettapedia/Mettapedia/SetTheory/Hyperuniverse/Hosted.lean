import Mettapedia.SetTheory.Hyperuniverse.Inside
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet

/-!
# Strong extensionality of the limit, and the copy inside one hyperset

A bisimulation of membership relates only equal points, because related points
agree at every finite stage. The picture of the limit is therefore injective.
The picture of the universal set belongs to itself, its members copy the
limit, and it is not a set of every hyperset.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set Topology TopologicalSpace
open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.SetTheory.Profiles
open Mettapedia.TypeTheory.MaterialSets.Hypersets

theorem member_iff_mem_decode (z p : N) : member z p ↔ z ∈ (decode p : Set N) := by
  rw [member, fixedHomeo_decode]

theorem coe_proj_succ (p : N) (n : ℕ) :
    (proj (n + 1) p : Set (Stage n)) = proj n '' (decode p : Set N) := by
  have hmap : (proj (n + 1) (encode (decode p)) : Set (Stage n)) =
      proj n '' (decode p : Set N) := by
    have hstage : proj (n + 1) (encode (decode p)) =
        Compacts.map (proj n) (proj_continuous n) (decode p) := by
      unfold encode proj encodeStage
      rfl
    rw [hstage]
    exact Compacts.coe_map (proj_continuous n) (decode p)
  simpa [encode_decode p] using hmap

/-- Related points of a membership bisimulation agree at every stage. -/
theorem proj_eq_of_related {R : N → N → Prop}
    (hR : IsBisimulation (memChild member) (memChild member) R)
    {x y : N} (hxy : R x y) (n : ℕ) : proj n x = proj n y := by
  have agree : ∀ n x y, R x y → proj n x = proj n y := by
    intro n
    induction n with
    | zero =>
      intro x y _
      exact Subsingleton.elim _ _
    | succ n ih =>
      intro x y hxy
      apply Compacts.ext
      ext s
      constructor
      · intro hs
        rw [coe_proj_succ] at hs
        rcases hs with ⟨z, hz, hs⟩
        obtain ⟨w, hw, hzw⟩ := (hR hxy).1 z ((member_iff_mem_decode z x).mpr hz)
        rw [coe_proj_succ]
        exact ⟨w, (member_iff_mem_decode w y).mp hw, (ih z w hzw).symm.trans hs⟩
      · intro hs
        rw [coe_proj_succ] at hs
        rcases hs with ⟨w, hw, hs⟩
        obtain ⟨z, hz, hzw⟩ := (hR hxy).2 w ((member_iff_mem_decode w y).mpr hw)
        rw [coe_proj_succ]
        exact ⟨z, (member_iff_mem_decode z x).mp hz, (ih z w hzw).trans hs⟩
  exact agree n x y hxy

/-- Every bisimulation of membership on the limit relates only equal points. -/
theorem stronglyExtensional_member : StronglyExtensional (memChild member) := by
  intro R hR x y hxy
  apply N.ext
  funext n
  exact proj_eq_of_related hR hxy n

theorem eq_of_bisimilar_member {x y : N}
    (h : Bisimilar (memChild member) (memChild member) x y) : x = y := by
  rcases h with ⟨R, hR, hxy⟩
  exact stronglyExtensional_member R hR x y hxy

/-- Membership in either direction: `x` belongs to `y` exactly when the picture
of `x` belongs to the picture of `y`. -/
theorem member_iff_decorateN_mem (x y : N) :
    member x y ↔ decorateN x ∈ decorateN y := by
  constructor
  · intro h
    exact HSet.decorate_mem_decorate h
  · intro h
    rcases decorateN_mem.mp h with ⟨x', hx', he⟩
    have hxeq : x' = x :=
      eq_of_bisimilar_member (HSet.decorate_eq_decorate_iff.mp he.symm)
    exact hxeq ▸ hx'

theorem decorateN_injective : Function.Injective decorateN :=
  fun _ _ h => eq_of_bisimilar_member (HSet.decorate_eq_decorate_iff.mp h)

/-- The picture of the universal set belongs to itself. -/
theorem decorateN_univ_mem_self : decorateN univSet ∈ decorateN univSet :=
  (member_iff_decorateN_mem univSet univSet).mp member_univ_self

/-- The picture of the universal set does not contain every hyperset. -/
theorem decorateN_univ_not_everything :
    ¬ ∀ x : HSet.{0}, x ∈ decorateN univSet :=
  fun h => HSet.not_exists_universal ⟨decorateN univSet, h⟩

theorem decorateN_not_surjective : ¬ Function.Surjective decorateN := by
  intro hsurj
  refine decorateN_univ_not_everything fun x => ?_
  rcases hsurj x with ⟨y, rfl⟩
  exact (member_iff_decorateN_mem y univSet).mp (member_univ y)

/-- The members of the picture of the universal set copy the limit. -/
theorem members_univ_iso :
    ∃ e : N ≃ {z : HSet.{0} // z ∈ decorateN univSet},
      ∀ x y, member x y ↔ (e x).1 ∈ (e y).1 := by
  let f : N → {z : HSet.{0} // z ∈ decorateN univSet} := fun x =>
    ⟨decorateN x, (member_iff_decorateN_mem x univSet).mp (member_univ x)⟩
  have hinj : Function.Injective f := fun x y h =>
    decorateN_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro ⟨z, hz⟩
    rcases decorateN_mem.mp hz with ⟨x, _, he⟩
    refine ⟨x, Subtype.ext ?_⟩
    show decorateN x = z
    exact he.symm
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x y
  simp only [f]
  exact member_iff_decorateN_mem x y

/-- A positive formula cuts out, inside the picture of the universal set, the
pictures of the points of its closed class. -/
theorem positive_comprehension_in_U (φ : Pos 1) :
    IsClosed (classOn φ) ∧
      (∀ x, decorateN x ∈ decorateN (setOfFormula φ) ↔ realize φ (fun _ => x)) ∧
      decorateN (setOfFormula φ) ∈ decorateN univSet :=
  ⟨classOn_closed φ,
    fun x =>
      ((member_iff_decorateN_mem x (setOfFormula φ)).symm).trans (member_setOfFormula φ x),
    (member_iff_decorateN_mem (setOfFormula φ) univSet).mp (member_univ _)⟩

/-- The hypersets host the limit: membership is kept in both directions. -/
theorem hypersets_host_N :
    ∃ d : N → HSet.{0}, Function.Injective d ∧ ∀ x y, member x y ↔ d x ∈ d y :=
  ⟨decorateN, decorateN_injective, member_iff_decorateN_mem⟩

/-- Separation holds for hyperset membership. -/
theorem hypersets_hasSeparation : HasSeparation (fun x y : HSet.{0} => x ∈ y) :=
  fun a P => ⟨HSet.sep P a, fun _ => HSet.mem_sep⟩

/-- The limit has a universal set. -/
theorem exists_universal_member : ∃ u : N, ∀ z, member z u :=
  ⟨univSet, member_univ⟩

/-- Separation and a universal set hold on opposite sides. -/
theorem theories_disagree :
    HasSeparation (fun x y : HSet.{0} => x ∈ y) ∧ ¬ HasSeparation member ∧
      (∃ u : N, ∀ z, member z u) ∧ ¬ ∃ V : HSet.{0}, ∀ x, x ∈ V :=
  ⟨hypersets_hasSeparation, not_separation, exists_universal_member, HSet.not_exists_universal⟩

example : decorateN quine ∈ decorateN quine :=
  (member_iff_decorateN_mem quine quine).mp ((member_quine quine).mpr rfl)

example : decorateN quine ≠ decorateN emptySet := by
  intro h
  have hmem : member quine emptySet := by
    rw [← decorateN_injective h]
    exact (member_quine quine).mpr rfl
  exact member_empty quine hmem

example : ¬ Bisimilar (memChild member) (memChild member) univSet emptySet :=
  not_bisimilar_of_child (member_univ emptySet) (member_empty)

end Mettapedia.SetTheory.Hyperuniverse
