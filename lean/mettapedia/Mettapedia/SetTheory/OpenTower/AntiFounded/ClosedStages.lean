import Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet

/-!
# Closed stages of the hypersets

A *closed stage* of the hypersets (`HClosed`) is a hyperset that is transitive and closed under
union, power set and replacement. It is the same closure as `ZFSetUniverseClosure.Closed` for
`ZFSet`, read on the anti-founded membership of `HSet`; replacement is stated relationally, as
in `InternalTower.ClosedRel`: a hyperset whose members lie in the stage and are the values of
a function on the members of a member is a member.

**The well-founded part of a closed stage is a closed set.** The well-founded members of a
hyperset, unwound into `ZFSet` (`HSet.toZFSet`), form a closed set whenever the hyperset is a
closed stage (`HClosed.closed_toZFSet`). A set is a member of that part exactly when its
hyperset is a member of the stage (`mem_toZFSet_iff`).

**The closed sets stay closed.** A set is closed exactly when its hyperset is a closed stage
(`hclosed_ofZFSet_iff`): union, power set and replacement of well-founded hypersets are the
operations of `ZFSet` (`HSet.ofZFSet_sUnion`, `HSet.ofZFSet_powerset`), and a subset of a
well-founded hyperset is well-founded. So every level `V_κ` of the von Neumann hierarchy that
is closed in `ZFSet` is a closed stage of the hypersets, unchanged.

A closed stage is closed under pairs (`HClosed.pair_mem`), by a case split on membership of
`∅`, as for `ZFSet`.

**Separating a closed stage.** A predicate is *stable* when it passes to members and holds of
every hyperset all of whose members satisfy it (`Stable`). Separating a closed stage by a stable
predicate gives a closed stage (`HClosed.sep_stable`). Well-foundedness is stable
(`stable_wf`), and so is well-foundedness *over* a hyperset `a` (`WFOver a`: every descending
membership path that avoids `a` as an intermediate step is finite), when the members of `a`
satisfy it (`stable_wfOver`).

**Controls.** The empty hyperset is a closed stage (`hclosed_empty`). `Ω` is not a closed stage:
its power set `{∅, Ω}` is not a member of it (`not_hclosed_quineAtom`). `{∅}` is transitive but
not a closed stage (`not_hclosed_singleton_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open scoped ZFSet

universe u

/-! ## Closed stages -/

/-- A closed stage of the hypersets: transitive, and closed under union, power set and
replacement, stated relationally. -/
structure HClosed (U : HSet.{u}) : Prop where
  /-- Members of members are members. -/
  transitive : ∀ ⦃x : HSet.{u}⦄, x ∈ U → ∀ ⦃y : HSet.{u}⦄, y ∈ x → y ∈ U
  /-- Closure under union. -/
  union_mem : ∀ ⦃x : HSet.{u}⦄, x ∈ U → HSet.sUnion x ∈ U
  /-- Closure under power set. -/
  power_mem : ∀ ⦃x : HSet.{u}⦄, x ∈ U → HSet.powerset x ∈ U
  /-- Closure under replacement: a hyperset whose members are in the stage and are the values
  of a function on the members of a member is a member. -/
  image_mem : ∀ ⦃a b : HSet.{u}⦄, a ∈ U → (∀ ⦃y : HSet.{u}⦄, y ∈ b → y ∈ U) →
    (∃ f : HSet.{u} → HSet.{u}, ∀ y, y ∈ b ↔ ∃ x ∈ a, f x = y) → b ∈ U

namespace HClosed

variable {U : HSet.{u}}

/-- A subset of a member is a member. -/
theorem subset_mem (hU : HClosed U) {a b : HSet.{u}} (ha : a ∈ U) (hb : b ⊆ a) : b ∈ U :=
  hU.transitive (hU.power_mem ha) (HSet.mem_powerset.mpr hb)

/-- A nonempty closed stage has the empty hyperset as a member. -/
theorem empty_mem (hU : HClosed U) {a : HSet.{u}} (ha : a ∈ U) : (∅ : HSet.{u}) ∈ U :=
  hU.subset_mem ha (HSet.subset_iff.mpr fun z hz => absurd hz (HSet.notMem_empty z))

/-- Separation inside a member gives a member. -/
theorem sep_mem (hU : HClosed U) {a : HSet.{u}} (ha : a ∈ U) (P : HSet.{u} → Prop) :
    HSet.sep P a ∈ U :=
  hU.subset_mem ha (HSet.subset_iff.mpr fun _ hz => (HSet.mem_sep.mp hz).1)

/-- A closed stage is closed under pairs: `{a, b}` is the image of `{∅, {∅}}` under the
function sending `∅` to `a` and every other hyperset to `b`. The case split is excluded
middle. -/
theorem pair_mem (hU : HClosed U) {a b : HSet.{u}} (ha : a ∈ U) (hb : b ∈ U) :
    ({a, b} : HSet.{u}) ∈ U := by
  classical
  have base : HSet.powerset (HSet.powerset (∅ : HSet.{u})) ∈ U :=
    hU.power_mem (hU.power_mem (hU.empty_mem ha))
  refine hU.image_mem base (fun y hy => ?_) ⟨fun z => if z = ∅ then a else b, fun y => ?_⟩
  · rcases HSet.mem_pair.mp hy with rfl | rfl
    · exact ha
    · exact hb
  · rw [HSet.mem_pair, HSet.powerset_empty]
    constructor
    · rintro (rfl | rfl)
      · refine ⟨∅, HSet.mem_powerset.mpr (HSet.subset_iff.mpr fun z hz =>
          absurd hz (HSet.notMem_empty z)), if_pos rfl⟩
      · refine ⟨{∅}, HSet.mem_powerset.mpr (HSet.subset_iff.mpr fun _ hz => hz), ?_⟩
        exact if_neg HSet.empty_ne_singleton_empty.symm
    · rintro ⟨z, _, rfl⟩
      by_cases hz : z = ∅
      · exact Or.inl (if_pos hz)
      · exact Or.inr (if_neg hz)

/-- Below a member, every hyperset reached by membership is a member. -/
theorem mem_of_reflTransGen (hU : HClosed U) {x z : HSet.{u}} (hx : x ∈ U)
    (h : Relation.ReflTransGen (fun a b : HSet.{u} => b ∈ a) x z) : z ∈ U := by
  induction h with
  | refl => exact hx
  | tail _ hmem ih => exact hU.transitive ih hmem

end HClosed

/-- The empty hyperset is a closed stage. -/
theorem hclosed_empty : HClosed (∅ : HSet.{u}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact absurd hx (HSet.notMem_empty x)
  · intro x hx
    exact absurd hx (HSet.notMem_empty x)
  · intro x hx
    exact absurd hx (HSet.notMem_empty x)
  · intro a _ ha
    exact absurd ha (HSet.notMem_empty a)

/-! ## The well-founded part of a closed stage -/

/-- A set is a member of the well-founded part of `U` exactly when its hyperset is a member
of `U`. -/
theorem mem_toZFSet_iff {U : HSet.{u}} {w : ZFSet.{u}} :
    w ∈ HSet.toZFSet U ↔ HSet.ofZFSet w ∈ U := by
  rw [← HSet.ofZFSet_mem_ofZFSet_iff, HSet.ofZFSet_toZFSet, HSet.mem_sep]
  exact ⟨fun h => h.1, fun h => ⟨h, HSet.wf_ofZFSet w⟩⟩

/-- The hyperset of the well-founded part of `U` is the separation of `U` by
well-foundedness; in particular it is included in `U`. -/
theorem ofZFSet_toZFSet_subset (U : HSet.{u}) : HSet.ofZFSet (HSet.toZFSet U) ⊆ U := by
  rw [HSet.ofZFSet_toZFSet]
  exact HSet.subset_iff.mpr fun _ hz => (HSet.mem_sep.mp hz).1

/-- **The well-founded part of a closed stage is a closed set.** -/
theorem HClosed.closed_toZFSet {U : HSet.{u}} (hU : HClosed U) : Closed (HSet.toZFSet U) where
  transitive := by
    intro y hy z hz
    rw [mem_toZFSet_iff] at hy ⊢
    exact hU.transitive hy (HSet.ofZFSet_mem_ofZFSet_iff.mpr hz)
  union_mem ha := by
    rw [mem_toZFSet_iff] at ha ⊢
    rw [HSet.ofZFSet_sUnion]
    exact hU.union_mem ha
  power_mem ha := by
    rw [mem_toZFSet_iff] at ha ⊢
    rw [HSet.ofZFSet_powerset]
    exact hU.power_mem ha
  replacement_mem := by
    intro a ha f hf
    rw [mem_toZFSet_iff] at ha ⊢
    refine hU.image_mem ha (fun y hy => ?_)
      ⟨fun y => HSet.ofZFSet (f (HSet.toZFSet y)), fun y => ?_⟩
    · obtain ⟨z, hz, rfl⟩ := HSet.mem_ofZFSet_iff.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hz
      exact mem_toZFSet_iff.mp (hf x hx)
    · rw [HSet.mem_ofZFSet_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hz
        exact ⟨HSet.ofZFSet x, HSet.ofZFSet_mem_ofZFSet_iff.mpr hx, by
          simp only [HSet.toZFSet_ofZFSet]⟩
      · rintro ⟨x', hx', rfl⟩
        obtain ⟨x, hx, rfl⟩ := HSet.mem_ofZFSet_iff.mp hx'
        exact ⟨f x, mem_replacement.mpr ⟨x, hx, rfl⟩, by simp only [HSet.toZFSet_ofZFSet]⟩

/-- **The closed sets stay closed.** A set is closed exactly when its hyperset is a closed
stage of the hypersets. -/
theorem hclosed_ofZFSet_iff {V : ZFSet.{u}} : HClosed (HSet.ofZFSet V) ↔ Closed V := by
  constructor
  · intro h
    have closed := h.closed_toZFSet
    rwa [HSet.toZFSet_ofZFSet] at closed
  · intro hV
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := HSet.mem_ofZFSet_iff.mp hx
      obtain ⟨y', hy', rfl⟩ := HSet.mem_ofZFSet_iff.mp hy
      exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (hV.transitive x' hx' hy')
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := HSet.mem_ofZFSet_iff.mp hx
      rw [← HSet.ofZFSet_sUnion]
      exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (hV.union_mem hx')
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := HSet.mem_ofZFSet_iff.mp hx
      rw [← HSet.ofZFSet_powerset]
      exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (hV.power_mem hx')
    · rintro a b ha hb ⟨f, hf⟩
      obtain ⟨a', ha', rfl⟩ := HSet.mem_ofZFSet_iff.mp ha
      have value : ∀ z ∈ a', ∃ w ∈ V, HSet.ofZFSet w = f (HSet.ofZFSet z) := fun z hz =>
        HSet.mem_ofZFSet_iff.mp
          (hb ((hf _).mpr ⟨_, HSet.ofZFSet_mem_ofZFSet_iff.mpr hz, rfl⟩))
      let g : ZFSet.{u} → ZFSet.{u} := fun z => HSet.toZFSet (f (HSet.ofZFSet z))
      have hg : ∀ z ∈ a', HSet.ofZFSet (g z) = f (HSet.ofZFSet z) := by
        intro z hz
        obtain ⟨w, _, hw⟩ := value z hz
        simp only [g, ← hw, HSet.toZFSet_ofZFSet]
      have hgV : ∀ z ∈ a', g z ∈ V := by
        intro z hz
        obtain ⟨w, hwV, hw⟩ := value z hz
        simp only [g, ← hw, HSet.toZFSet_ofZFSet]
        exact hwV
      have equal : b = HSet.ofZFSet (replacement a' g) := by
        ext y
        rw [hf y, HSet.mem_ofZFSet_iff]
        constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨z, hz, rfl⟩ := HSet.mem_ofZFSet_iff.mp hx
          exact ⟨g z, mem_replacement.mpr ⟨z, hz, rfl⟩, hg z hz⟩
        · rintro ⟨w, hw, rfl⟩
          obtain ⟨z, hz, rfl⟩ := mem_replacement.mp hw
          exact ⟨HSet.ofZFSet z, HSet.ofZFSet_mem_ofZFSet_iff.mpr hz, (hg z hz).symm⟩
      rw [equal]
      exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (hV.replacement_mem ha' g hgV)

/-! ## Stable separation -/

/-- A predicate on hypersets is stable when it passes to members and holds of every hyperset
all of whose members satisfy it. -/
structure Stable (P : HSet.{u} → Prop) : Prop where
  /-- The predicate passes to members. -/
  mem : ∀ ⦃x : HSet.{u}⦄, P x → ∀ ⦃y : HSet.{u}⦄, y ∈ x → P y
  /-- The predicate holds of a hyperset whose members all satisfy it. -/
  of_forall_mem : ∀ ⦃x : HSet.{u}⦄, (∀ ⦃y : HSet.{u}⦄, y ∈ x → P y) → P x

/-- **Separating a closed stage by a stable predicate gives a closed stage.** -/
theorem HClosed.sep_stable {U : HSet.{u}} {P : HSet.{u} → Prop} (hU : HClosed U)
    (hP : Stable P) : HClosed (HSet.sep P U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨hxU, hPx⟩ := HSet.mem_sep.mp hx
    exact HSet.mem_sep.mpr ⟨hU.transitive hxU hy, hP.mem hPx hy⟩
  · intro x hx
    obtain ⟨hxU, hPx⟩ := HSet.mem_sep.mp hx
    refine HSet.mem_sep.mpr ⟨hU.union_mem hxU, hP.of_forall_mem fun y hy => ?_⟩
    obtain ⟨z, hz, hyz⟩ := HSet.mem_sUnion.mp hy
    exact hP.mem (hP.mem hPx hz) hyz
  · intro x hx
    obtain ⟨hxU, hPx⟩ := HSet.mem_sep.mp hx
    refine HSet.mem_sep.mpr ⟨hU.power_mem hxU, hP.of_forall_mem fun y hy => ?_⟩
    exact hP.of_forall_mem fun z hz => hP.mem hPx (HSet.subset_iff.mp (HSet.mem_powerset.mp hy) hz)
  · rintro a b ha hb himage
    have hbU : ∀ ⦃y : HSet.{u}⦄, y ∈ b → y ∈ U := fun y hy => (HSet.mem_sep.mp (hb hy)).1
    exact HSet.mem_sep.mpr ⟨hU.image_mem (HSet.mem_sep.mp ha).1 hbU himage,
      hP.of_forall_mem fun y hy => (HSet.mem_sep.mp (hb hy)).2⟩

/-- Well-foundedness is stable. -/
theorem stable_wf : Stable (HSet.WF : HSet.{u} → Prop) :=
  ⟨fun _ hx _ hy => hx.mem hy, fun _ h => HSet.wf_of_forall_mem fun _ hy => h hy⟩

/-- Separating a closed stage by well-foundedness gives its well-founded part. -/
theorem sep_wf_eq_ofZFSet_toZFSet (U : HSet.{u}) :
    HSet.sep HSet.WF U = HSet.ofZFSet (HSet.toZFSet U) :=
  (HSet.ofZFSet_toZFSet U).symm

/-- Well-foundedness over `a`: every descending membership path from `x` is finite, except
that it may stop at `a`. The membership steps out of `a` are not followed. -/
def WFOver (a x : HSet.{u}) : Prop :=
  Acc (fun z w : HSet.{u} => z ∈ w ∧ w ≠ a) x

/-- `a` itself is well-founded over `a`. -/
theorem wfOver_self (a : HSet.{u}) : WFOver a a :=
  Acc.intro a fun _ h => absurd rfl h.2

/-- A well-founded hyperset is well-founded over every hyperset. -/
theorem wfOver_of_wf {x : HSet.{u}} (hx : x.WF) (a : HSet.{u}) : WFOver a x :=
  Subrelation.accessible (fun h => h.1) hx

/-- A self-member other than `a` is not well-founded over `a`. -/
theorem not_wfOver_of_mem_self {a x : HSet.{u}} (hx : x ∈ x) (hne : x ≠ a) : ¬ WFOver a x :=
  not_acc_of_rel_self (r := fun z w : HSet.{u} => z ∈ w ∧ w ≠ a) ⟨hx, hne⟩

/-- Well-foundedness over `a` is stable when every member of `a` is well-founded over `a`. -/
theorem stable_wfOver {a : HSet.{u}} (ha : ∀ ⦃z : HSet.{u}⦄, z ∈ a → WFOver a z) :
    Stable (WFOver a) := by
  refine ⟨fun x hx y hy => ?_, fun x h => Acc.intro x fun y hy => h hy.1⟩
  by_cases same : x = a
  · subst same
    exact ha hy
  · exact hx.inv ⟨hy, same⟩

/-! ## Controls -/

/-- `Ω` is not a closed stage: its power set `{∅, Ω}` is not `Ω`. -/
theorem not_hclosed_quineAtom : ¬ HClosed HSet.quineAtom.{u} := by
  intro h
  have member := h.empty_mem HSet.quineAtom_mem_self
  exact HSet.empty_ne_quineAtom (HSet.mem_quineAtom.mp member)

/-- `{∅}` is transitive but not a closed stage: the power set of `∅` is `{∅}`, which is not a
member of `{∅}`. -/
theorem not_hclosed_singleton_empty : ¬ HClosed ({∅} : HSet.{u}) := by
  intro h
  have member := h.power_mem (HSet.mem_singleton_self ∅)
  rw [HSet.powerset_empty, HSet.mem_singleton] at member
  exact HSet.empty_ne_singleton_empty member.symm

/-- `{∅}` is transitive: its only member, `∅`, has no members. -/
example : ∀ ⦃x : HSet.{u}⦄, x ∈ ({∅} : HSet.{u}) → ∀ ⦃y : HSet.{u}⦄, y ∈ x →
    y ∈ ({∅} : HSet.{u}) := by
  intro x hx y hy
  rw [HSet.mem_singleton] at hx
  subst hx
  exact absurd hy (HSet.notMem_empty y)

/-- The hyperset of the hereditarily finite sets is a closed stage. -/
example : HClosed (HSet.ofZFSet (V_ Ordinal.omega0) : HSet.{u}) :=
  hclosed_ofZFSet_iff.mpr ((Strength.InaccessibleLevels.closed_iff _).mpr (Or.inr (Or.inl rfl)))

#print axioms HClosed.closed_toZFSet
#print axioms hclosed_ofZFSet_iff
#print axioms HClosed.sep_stable
#print axioms stable_wfOver

end Mettapedia.SetTheory.OpenTower.AntiFounded
