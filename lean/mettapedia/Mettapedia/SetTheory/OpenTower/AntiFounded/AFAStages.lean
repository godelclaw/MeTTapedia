import Mettapedia.SetTheory.OpenTower.AntiFounded.Classification

/-!
# Stages closed under anti-foundation: one chain at the inaccessible heights

A closed stage (`HClosed`) is closed under the operations of `ZFSet`. Anti-foundation adds one
more operation: a graph of small size has a decoration. A stage is *closed under
anti-foundation* (`AFAClosed`) when, moreover, every graph whose nodes are fewer than the members
of one of its members is decorated inside the stage.

**A small picture.** For `κ` regular and uncountable, a hereditarily small hyperset is the
picture of a graph with fewer than `κ` nodes (`exists_small_picture`): the paths of its tree of
memberships of each length are fewer than `κ` by regularity, and there are countably many
lengths.

**The chain comes back.** `B_κ` is closed under anti-foundation for `κ = ℵ₀` and for `κ`
inaccessible (`afaClosed_branching`). A nonempty stage closed under anti-foundation contains `Ω`
(`AFAClosed.quineAtom_mem`), so no closed set of `ZFSet` other than `∅` is one
(`not_afaClosed_ofZFSet`). At an inaccessible height `κ` the stage closed under anti-foundation
is unique: it is `B_κ` (`afaClosed_iff_eq_branching`). So the stages closed under
anti-foundation at inaccessible heights form one chain (`afaClosed_subset_total`), and every
hyperset lies in one exactly when there are cofinally many inaccessibles
(`exists_afaClosed_mem`). Their well-founded parts are the `V_κ` (`toZFSet_branching`).

The height `ω` is not covered by the uniqueness theorem: `B_ℵ₀` is closed under anti-foundation,
and whether a smaller stage of height `ω` is (the hypersets with a finite picture) is not
decided here.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-! ## A hereditarily small hyperset has a small picture -/

section SmallPicture

variable {κ : Cardinal.{u}} {x : HSet.{u}}

/-- The paths of length `n` in the tree of memberships of `x` that name a hyperset. -/
def ValidPaths (κ : Cardinal.{u}) (x : HSet.{u}) (n : ℕ) : Type u :=
  {l : List κ.ord.ToType // l.length = n ∧ unfoldValue κ x l ≠ none}

theorem unfoldValue_ne_none_of_cons {t : κ.ord.ToType} {l : List κ.ord.ToType}
    (h : unfoldValue κ x (t :: l) ≠ none) : unfoldValue κ x l ≠ none := by
  intro hl
  apply h
  simp only [unfoldValue, hl, Option.bind_none]

/-- **The paths of each length are fewer than `κ`**, for `κ` regular. -/
theorem mk_validPaths_lt (hreg : κ.IsRegular) (hx : HerSmall κ x) :
    ∀ n, #(ValidPaths κ x n) < κ
  | 0 => by
    have single : Subsingleton (ValidPaths κ x 0) :=
      ⟨fun a b => Subtype.ext (by
        rw [List.length_eq_zero_iff.mp a.2.1, List.length_eq_zero_iff.mp b.2.1])⟩
    exact (le_one_iff_subsingleton.mpr single).trans_lt
      (one_lt_aleph0.trans_le hreg.aleph0_le)
  | n + 1 => by
    have ih := mk_validPaths_lt hreg hx n
    let F : (Σ l : ValidPaths κ x n, {t : κ.ord.ToType // unfoldValue κ x (t :: l.1) ≠ none}) →
        ValidPaths κ x (n + 1) :=
      fun p => ⟨p.2.1 :: p.1.1, by rw [List.length_cons, p.1.2.1], p.2.2⟩
    have surjective : Function.Surjective F := by
      rintro ⟨l', hlen, hne⟩
      cases l' with
      | nil => exact absurd hlen (by simp)
      | cons t l =>
        refine ⟨⟨⟨l, by simpa using hlen, unfoldValue_ne_none_of_cons hne⟩, ⟨t, hne⟩⟩, rfl⟩
    have fiber : ∀ l : ValidPaths κ x n,
        #{t : κ.ord.ToType // unfoldValue κ x (t :: l.1) ≠ none} < κ := by
      intro l
      obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp l.2.2
      have hs : SmallMembers κ z := hx z (below_of_unfoldValue κ x hz)
      have equal : ∀ t, unfoldValue κ x (t :: l.1) = enumOf κ z t := fun t => by
        simp only [unfoldValue, hz, Option.bind_some]
      simp only [equal]
      exact enumOf_support κ hs
    calc #(ValidPaths κ x (n + 1))
        ≤ #(Σ l : ValidPaths κ x n, {t : κ.ord.ToType // unfoldValue κ x (t :: l.1) ≠ none}) :=
          mk_le_of_surjective surjective
      _ = sum fun l : ValidPaths κ x n =>
            #{t : κ.ord.ToType // unfoldValue κ x (t :: l.1) ≠ none} := mk_sigma _
      _ < κ := sum_lt_of_isRegular hreg ih fiber

/-- **All the paths that name a hyperset are fewer than `κ`**, for `κ` regular and
uncountable. -/
theorem mk_validPaths_all_lt (hreg : κ.IsRegular) (hω : ℵ₀ < κ) (hx : HerSmall κ x) :
    #{l : List κ.ord.ToType // unfoldValue κ x l ≠ none} < κ := by
  let F : (Σ n : ℕ, ValidPaths κ x n) → {l : List κ.ord.ToType // unfoldValue κ x l ≠ none} :=
    fun p => ⟨p.2.1, p.2.2.2⟩
  have surjective : Function.Surjective F := fun l => ⟨⟨l.1.length, ⟨l.1, rfl, l.2⟩⟩, rfl⟩
  calc #{l : List κ.ord.ToType // unfoldValue κ x l ≠ none}
      ≤ #(Σ n : ℕ, ValidPaths κ x n) := mk_le_of_surjective surjective
    _ = sum fun n : ℕ => #(ValidPaths κ x n) := mk_sigma _
    _ < κ := sum_lt_lift_of_isRegular hreg (by rwa [mk_nat, lift_aleph0])
        (mk_validPaths_lt hreg hx)

theorem unfoldValue_ne_none_of_reachable {l : List κ.ord.ToType}
    (h : Relation.ReflTransGen (unfoldEdge κ x) [] l) : unfoldValue κ x l ≠ none := by
  induction h with
  | refl => simp only [unfoldValue, ne_eq, reduceCtorEq, not_false_eq_true]
  | tail _ hedge _ =>
    obtain ⟨_, rfl, hne⟩ := hedge
    exact hne

/-- **A hereditarily small hyperset is the picture of a graph with fewer than `κ` nodes**, for
`κ` regular and uncountable. -/
theorem exists_small_picture (hreg : κ.IsRegular) (hω : ℵ₀ < κ) (hx : HerSmall κ x) :
    ∃ G : AccessiblePointedGraph.{u}, #G.Node < κ ∧ HSet.mk G = x := by
  refine ⟨AccessiblePointedGraph.generated (unfoldEdge κ x) [], ?_, ?_⟩
  · have injective : Function.Injective
        (fun l : (AccessiblePointedGraph.generated (unfoldEdge κ x) []).Node =>
          (⟨l.1, unfoldValue_ne_none_of_reachable l.2⟩ :
            {l : List κ.ord.ToType // unfoldValue κ x l ≠ none})) :=
      fun a b e => Subtype.ext (congrArg
        (fun p : {l : List κ.ord.ToType // unfoldValue κ x l ≠ none} => p.1) e)
    exact (mk_le_of_injective injective).trans_lt (mk_validPaths_all_lt hreg hω hx)
  · have equal := congrFun (isDecoration_unfold κ x hx).eq_decorate []
    exact equal.symm

end SmallPicture

/-! ## Stages closed under anti-foundation -/

/-- A closed stage in which every graph whose nodes are fewer than the members of a member is
decorated. -/
structure AFAClosed (U : HSet.{u}) : Prop extends HClosed U where
  /-- A graph whose nodes inject into the members of a member is decorated in the stage. -/
  decorate_mem : ∀ ⦃x : HSet.{u}⦄, x ∈ U → ∀ {α : Type u} (r : α → α → Prop),
    (∃ g : α → HSet.{u}, Function.Injective g ∧ ∀ a, g a ∈ x) → ∀ a, HSet.decorate r a ∈ U

/-- **`B_κ` is closed under anti-foundation**, for `κ = ℵ₀` and for `κ` inaccessible. -/
theorem afaClosed_branching {κ : Cardinal.{u}} (hκ : κ = ℵ₀ ∨ κ.IsInaccessible) :
    AFAClosed (branching κ) := by
  refine ⟨hclosed_branching_iff.mpr (Or.inr hκ), ?_⟩
  intro x hx α r ⟨g, injective, hg⟩ a
  obtain ⟨ι, g', hg', hxg'⟩ := exists_injective_members x
  have small := (smallMembers_iff_of_injective hg' hxg').mp (mem_branching.mp hx).smallMembers
  have hit : ∀ b, ∃ i, g' i = g b := fun b => (hxg' _).mp (hg b)
  choose φ hφ using hit
  have φinjective : Function.Injective φ := fun b b' e =>
    injective ((hφ b).symm.trans ((congrArg g' e).trans (hφ b')))
  exact decorate_mem_branching r ((mk_le_of_injective φinjective).trans_lt small) a

/-- **A nonempty stage closed under anti-foundation contains `Ω`.** -/
theorem AFAClosed.quineAtom_mem {U : HSet.{u}} (hU : AFAClosed U) {x : HSet.{u}} (hx : x ∈ U) :
    HSet.quineAtom ∈ U := by
  have hEmpty := hU.toHClosed.empty_mem hx
  have hSingle : ({∅} : HSet.{u}) ∈ U := by
    rw [← HSet.powerset_empty]
    exact hU.toHClosed.power_mem hEmpty
  have member := hU.decorate_mem hSingle HSet.loop.edge
    ⟨fun _ => ∅, fun _ _ _ => rfl, fun _ => HSet.mem_singleton_self ∅⟩
    HSet.loop.point
  rwa [HSet.decorate_loop] at member

/-- **No closed set of `ZFSet` other than `∅` is closed under anti-foundation.** -/
theorem not_afaClosed_ofZFSet {V : ZFSet.{u}} (hV : V ≠ ∅) : ¬ AFAClosed (HSet.ofZFSet V) := by
  intro h
  obtain ⟨w, hw⟩ : ∃ w, w ∈ V := by
    by_contra none
    exact hV ((ZFSet.eq_empty V).mpr fun y hy => none ⟨y, hy⟩)
  have member := h.quineAtom_mem (HSet.ofZFSet_mem_ofZFSet_iff.mpr hw)
  exact HSet.not_wf_quineAtom ((HSet.wf_ofZFSet V).mem member)

/-- **At an inaccessible height, the stage closed under anti-foundation is `B_κ`.** -/
theorem AFAClosed.eq_branching {U : HSet.{u}} (hU : AFAClosed U) {κ : Cardinal.{u}}
    (hκ : κ.IsInaccessible) (hW : HSet.toZFSet U = V_ κ.ord) : U = branching κ := by
  apply HSet.ext
  intro y
  constructor
  · intro hy
    exact mem_branching.mpr fun z hz =>
      hU.toHClosed.smallMembers_of_mem hW hκ.ne_zero (hU.toHClosed.mem_of_reflTransGen hy hz)
  · intro hy
    obtain ⟨G, hG, rfl⟩ := exists_small_picture hκ.isRegular hκ.aleph0_lt (mem_branching.mp hy)
    have hx : HSet.ofZFSet (#G.Node).ord.toZFSet ∈ U := by
      rw [← mem_toZFSet_iff, hW, ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
      exact ord_lt_ord.mpr hG
    obtain ⟨e⟩ := Cardinal.eq.mp (mk_ord_toType #G.Node).symm
    let g : G.Node → HSet.{u} := fun n =>
      HSet.ofZFSet ((Ordinal.typein (α := (#G.Node).ord.ToType) (· < ·)).toRelEmbedding
        (e n)).toZFSet
    have injective : Function.Injective g := fun n n' equal =>
      e.injective (Ordinal.typein_injective _
        (Ordinal.toZFSet_injective (HSet.ofZFSet_injective equal)))
    have members : ∀ n, g n ∈ HSet.ofZFSet (#G.Node).ord.toZFSet := fun n =>
      HSet.ofZFSet_mem_ofZFSet_iff.mpr
        (Ordinal.mem_toZFSet_iff.mpr ⟨_, Ordinal.typein_lt_self _, rfl⟩)
    have decorated := hU.decorate_mem hx G.edge ⟨g, injective, members⟩ G.point
    rwa [← HSet.mk_eq_decorate] at decorated

/-- **Closure under anti-foundation at an inaccessible height is the equation `U = B_κ`.** -/
theorem afaClosed_iff_eq_branching {U : HSet.{u}} {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    (hW : HSet.toZFSet U = V_ κ.ord) : AFAClosed U ↔ U = branching κ := by
  constructor
  · exact fun h => h.eq_branching hκ hW
  · rintro rfl
    exact afaClosed_branching (Or.inr hκ)

/-- **The stages closed under anti-foundation at inaccessible heights form one chain.** -/
theorem afaClosed_subset_total {U V : HSet.{u}} (hU : AFAClosed U) (hV : AFAClosed V)
    {κ μ : Cardinal.{u}} (hκ : κ.IsInaccessible) (hμ : μ.IsInaccessible)
    (hUW : HSet.toZFSet U = V_ κ.ord) (hVW : HSet.toZFSet V = V_ μ.ord) : U ⊆ V ∨ V ⊆ U := by
  rw [hU.eq_branching hκ hUW, hV.eq_branching hμ hVW]
  rcases le_total κ μ with h | h
  · exact Or.inl (branching_mono h)
  · exact Or.inr (branching_mono h)

/-- **Under cofinally many inaccessibles, every hyperset lies in a stage closed under
anti-foundation.** -/
theorem exists_afaClosed_mem (h : CofinalInaccessibles.{u}) (x : HSet.{u}) :
    ∃ U, AFAClosed U ∧ x ∈ U := by
  obtain ⟨G, rfl⟩ := HSet.exists_mk x
  obtain ⟨κ, hκ, above⟩ := h (#G.Node).ord
  exact ⟨branching κ, afaClosed_branching (Or.inr hκ),
    mem_branching.mpr (herSmall_mk G (ord_lt_ord.mp above))⟩

/-- The hyperset of `V_ω` is a closed stage that is not closed under anti-foundation. -/
example : HClosed (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) ∧
    ¬ AFAClosed (HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u})) := by
  refine ⟨hclosed_ofZFSet_iff.mpr ((closed_iff _).mpr (Or.inr (Or.inl rfl))),
    not_afaClosed_ofZFSet fun h => ?_⟩
  have member : (∅ : ZFSet.{u}) ∈ V_ Ordinal.omega0 := by
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_empty]
    exact Ordinal.omega0_pos
  rw [h] at member
  exact ZFSet.notMem_empty _ member

#print axioms exists_small_picture
#print axioms afaClosed_branching
#print axioms AFAClosed.quineAtom_mem
#print axioms not_afaClosed_ofZFSet
#print axioms AFAClosed.eq_branching
#print axioms afaClosed_iff_eq_branching
#print axioms afaClosed_subset_total
#print axioms exists_afaClosed_mem

end Mettapedia.SetTheory.OpenTower.AntiFounded
