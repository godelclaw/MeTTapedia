import Mettapedia.SetTheory.OpenTower.AntiFounded.Hosting
import Mettapedia.SetTheory.OpenTower.Potentialism.Transfer

/-!
# The modal logic of the closed stages: buttons

With access by inclusion, the closed stages of the hypersets validate `.2` and refute `.3`
(`valid_dot2_hclosed`, `not_valid_dot3_hclosed`). This module gives an upper bound.

**Buttons.** The jewels `J_k = {J_k, k}`, one for each natural number `k` (`jewel`), are
pairwise distinct self-members (`jewel_injective`, `jewel_mem_self`) and hereditarily finitely
branching (`jewel_mem_branching`). "`J_k` is in the stage" is a pure button: once pushed it stays
pushed, and the buttons are independent. From any closed stage `A`, and any set `S` of indices
containing those already in `A`, there is a closed stage `B ⊇ A` whose jewels with index below
`n` are exactly those in `S` (`exists_stage_with_jewels`). The stage is cut out of a `B_ν` by the
predicate "every descending membership path is finite unless it reaches `A` or a chosen jewel",
which is stable (`stable_accExcept`).

**Every finite Boolean algebra is a bounded-morphic image.** So, for each `n`, sending a stage
to its set of jewels below `n` is a surjective bounded morphism onto the Boolean algebra of
subsets of `Fin n` (`stage_onto_powerset`), and every formula valid on the closed stages is
valid on every finite Boolean algebra (`valid_powerset_of_valid_hclosed`). No large-cardinal
hypothesis is used: the buttons are already at height `ω`.

**The McKinsey schema separates.** Every finite Boolean algebra validates `.1`,
`□◇φ → ◇□φ` (`valid_dot1_powerset`), since its top is accessible from every world. Under
cofinally many inaccessibles the closed stages refute it (`not_valid_dot1_hclosed`): every stage
lies below some `B_ν`, and above every stage there is a closed stage that is no `B_ν`
(`exists_extension_not_branching`). So the logic of the stages contains the schemas K, T, 4 and
`.2`, lacks `.3` and `.1`, and is strictly contained in the logic of the finite Boolean algebras.

The exact logic is not identified here. Hamkins and Löwe show that independent buttons together
with *switches* bound the validities by S4.2; switches are not constructed here.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.SetTheory.OpenTower.Potentialism
open Cardinal
open scoped ZFSet

universe u

/-! ## Jewels -/

/-- The well-founded tag of the `k`-th jewel: the ordinal `k`. -/
noncomputable def jewelTag (k : ℕ) : HSet.{u} :=
  HSet.ofZFSet ((k : Ordinal.{u}).toZFSet)

theorem jewelTag_wf (k : ℕ) : (jewelTag.{u} k).WF :=
  HSet.wf_ofZFSet _

theorem jewelTag_injective : Function.Injective jewelTag.{u} := fun _ _ h =>
  Nat.cast_injective (R := Ordinal.{u})
    (Ordinal.toZFSet_injective (HSet.ofZFSet_injective h))

/-- The `k`-th jewel `J_k = {J_k, k}`: the self-loop at `k`, with the tag `k`. -/
noncomputable def jewel (k : ℕ) : HSet.{u} :=
  decorateWith (fun a b : ULift.{u} ℕ => a = b) (fun a => jewelTag a.down) ⟨k⟩

theorem mem_jewel {k : ℕ} {y : HSet.{u}} : y ∈ jewel k ↔ y = jewel k ∨ y = jewelTag k := by
  unfold jewel
  rw [mem_decorateWith]
  constructor
  · rintro (⟨b, rfl, rfl⟩ | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨_, rfl, rfl⟩
    · exact Or.inr rfl

theorem jewel_mem_self (k : ℕ) : jewel.{u} k ∈ jewel k :=
  mem_jewel.mpr (Or.inl rfl)

theorem not_wf_jewel (k : ℕ) : ¬ (jewel.{u} k).WF :=
  HSet.not_wf_of_mem_self (jewel_mem_self k)

theorem jewel_injective : Function.Injective jewel.{u} := by
  intro k m h
  have member : jewelTag.{u} k ∈ jewel m := h ▸ mem_jewel.mpr (Or.inr rfl)
  rcases mem_jewel.mp member with e | e
  · exact absurd (e ▸ jewelTag_wf k) (not_wf_jewel m)
  · exact jewelTag_injective e

theorem below_jewel {k : ℕ} {z : HSet.{u}} (h : Below (jewel k) z) :
    z = jewel k ∨ Below (jewelTag k) z := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hmem ih =>
    rcases ih with rfl | below
    · rcases mem_jewel.mp hmem with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr .refl
    · exact Or.inr (below.tail hmem)

theorem jewel_mem_branching (k : ℕ) : jewel.{u} k ∈ branching ℵ₀ := by
  refine mem_branching.mpr fun z hz => ?_
  rcases below_jewel hz with rfl | below
  · refine ⟨ULift.{u} Bool, fun b => if b.down then jewel k else jewelTag k,
      lt_aleph0_of_finite _, fun y => ?_⟩
    rw [mem_jewel]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨⟨true⟩, rfl⟩
      · exact ⟨⟨false⟩, rfl⟩
    · rintro ⟨⟨b⟩, rfl⟩
      cases b
      · exact Or.inr rfl
      · exact Or.inl rfl
  · have small : HerSmall ℵ₀ (jewelTag.{u} k) := herSmall_ofZFSet_toZFSet (by
      rw [Ordinal.card_nat]
      exact natCast_lt_aleph0)
    exact small z below

/-! ## Stages with a prescribed set of jewels -/

/-- Accessibility of membership, with the steps out of the hypersets satisfying `E` not
followed. -/
def AccExcept (E : HSet.{u} → Prop) (x : HSet.{u}) : Prop :=
  Acc (fun z w : HSet.{u} => z ∈ w ∧ ¬ E w) x

theorem accExcept_of_mem {E : HSet.{u} → Prop} {x : HSet.{u}} (hx : E x) : AccExcept E x :=
  Acc.intro x fun _ h => absurd hx h.2

/-- If the members of each hyperset satisfying `E` satisfy `E` or are well-founded, then
accessibility except at `E` is stable. -/
theorem stable_accExcept {E : HSet.{u} → Prop}
    (hE : ∀ ⦃x : HSet.{u}⦄, E x → ∀ ⦃y : HSet.{u}⦄, y ∈ x → E y ∨ y.WF) :
    Stable (AccExcept E) := by
  classical
  refine ⟨fun x hx y hy => ?_, fun x h => Acc.intro x fun y hy => h hy.1⟩
  by_cases hEx : E x
  · rcases hE hEx hy with hEy | hwf
    · exact accExcept_of_mem hEy
    · exact Subrelation.accessible (fun h => h.1) hwf
  · exact hx.inv ⟨hy, hEx⟩

/-- A closed stage lies in a closed `B_ν` with `ℵ₀ ≤ ν`. -/
theorem exists_branching_above {A : HSet.{u}} (hA : HClosed A) :
    ∃ ν : Cardinal.{u}, HClosed (branching ν) ∧ A ⊆ branching ν ∧ ℵ₀ ≤ ν := by
  rcases hclosed_classification hA with rfl | ⟨κ, hκ, _, _, hAκ⟩
  · exact ⟨ℵ₀, hclosed_branching_aleph0, hset_empty_subset _, le_rfl⟩
  · refine ⟨κ, hclosed_branching_iff.mpr (Or.inr hκ), hAκ, ?_⟩
    rcases hκ with rfl | hκ
    · exact le_rfl
    · exact hκ.aleph0_lt.le

/-- **From any closed stage, any larger set of jewels below `n` is reached exactly.** -/
theorem exists_stage_with_jewels {A : HSet.{u}} (hA : HClosed A) (n : ℕ) (S : Set (Fin n))
    (hS : ∀ i : Fin n, jewel i.val ∈ A → i ∈ S) :
    ∃ B : HSet.{u}, HClosed B ∧ A ⊆ B ∧ ∀ i : Fin n, jewel i.val ∈ B ↔ i ∈ S := by
  classical
  obtain ⟨ν, hν, hAν, hω⟩ := exists_branching_above hA
  let E : HSet.{u} → Prop := fun w => w ∈ A ∨ ∃ i ∈ S, w = jewel i.val
  have hE : ∀ ⦃x : HSet.{u}⦄, E x → ∀ ⦃y : HSet.{u}⦄, y ∈ x → E y ∨ y.WF := by
    rintro x (hx | ⟨i, hi, rfl⟩) y hy
    · exact Or.inl (Or.inl (hA.transitive hx hy))
    · rcases mem_jewel.mp hy with rfl | rfl
      · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      · exact Or.inr (jewelTag_wf _)
  refine ⟨HSet.sep (AccExcept E) (branching ν), hν.sep_stable (stable_accExcept hE),
    HSet.subset_iff.mpr fun x hx => HSet.mem_sep.mpr
      ⟨HSet.subset_iff.mp hAν hx, accExcept_of_mem (Or.inl hx)⟩, fun i => ?_⟩
  rw [HSet.mem_sep]
  constructor
  · rintro ⟨_, hacc⟩
    by_contra notIn
    have notE : ¬ E (jewel i.val) := by
      rintro (hA' | ⟨j, hj, e⟩)
      · exact notIn (hS i hA')
      · have same : i = j := Fin.ext (jewel_injective e)
        exact notIn (same ▸ hj)
    exact not_acc_of_rel_self (r := fun z w : HSet.{u} => z ∈ w ∧ ¬ E w)
      ⟨jewel_mem_self _, notE⟩ hacc
  · intro hi
    exact ⟨HSet.subset_iff.mp (branching_mono hω) (jewel_mem_branching _),
      accExcept_of_mem (Or.inr ⟨i, hi, rfl⟩)⟩

/-! ## Onto the finite Boolean algebras -/

/-- **The closed stages map onto the subsets of `Fin n` by a surjective bounded morphism**: a
stage goes to its set of jewels below `n`. -/
theorem stage_onto_powerset (n : ℕ) :
    ∃ f : {U : HSet.{u} // HClosed U} → Set (Fin n),
      (∀ S, ∃ A, f A = S) ∧ (∀ A B, A.1 ⊆ B.1 → f A ⊆ f B) ∧
        (∀ A S, f A ⊆ S → ∃ B, A.1 ⊆ B.1 ∧ f B = S) := by
  refine ⟨fun A => {i | jewel i.val ∈ A.1}, fun S => ?_, fun A B h i hi =>
    HSet.subset_iff.mp h hi, fun A S hAS => ?_⟩
  · obtain ⟨B, hB, _, hjewels⟩ := exists_stage_with_jewels hclosed_empty n S
      fun i h => absurd h (HSet.notMem_empty _)
    exact ⟨⟨B, hB⟩, Set.ext hjewels⟩
  · obtain ⟨B, hB, hAB, hjewels⟩ := exists_stage_with_jewels A.2 n S fun i h => hAS h
    exact ⟨⟨B, hB⟩, hAB, Set.ext hjewels⟩

/-- **Every formula valid on the closed stages is valid on every finite Boolean algebra.** -/
theorem valid_powerset_of_valid_hclosed {φ : Formula}
    (h : Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) φ) (n : ℕ) :
    Valid (fun S T : Set (Fin n) => S ⊆ T) φ := by
  obtain ⟨f, hsurj, hforth, hback⟩ := stage_onto_powerset.{u} n
  exact valid_of_surjective_bounded f hsurj hforth hback h

/-! ## The McKinsey schema separates the stages from the finite Boolean algebras -/

/-- The closed stages validate T and 4: inclusion is reflexive and transitive. -/
theorem valid_T_four_hclosed (φ : Formula) :
    Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) (Formula.axiomT φ) ∧
      Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) (Formula.axiomFour φ) :=
  ⟨valid_T_of_refl (R := fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1)
      (fun _ => HSet.subset_iff.mpr fun _ h => h) φ,
    valid_four_of_trans (R := fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1)
      (fun _ _ _ h₁ h₂ => hset_subset_trans h₁ h₂) φ⟩

/-- The McKinsey schema `.1`: `□◇φ → ◇□φ`. -/
def axiomDot1 (φ : Formula) : Formula :=
  Formula.impl (Formula.box (Formula.diamond φ)) (Formula.diamond (Formula.box φ))

/-- `.1` is valid on every finite Boolean algebra: the top is accessible from every world. -/
theorem valid_dot1_powerset (n : ℕ) (φ : Formula) :
    Valid (fun S T : Set (Fin n) => S ⊆ T) (axiomDot1 φ) := by
  intro V S
  simp only [axiomDot1, forces_impl, forces_box, forces_diamond]
  intro h
  refine ⟨Set.univ, Set.subset_univ _, fun T hT => ?_⟩
  obtain rfl := Set.eq_univ_of_univ_subset hT
  obtain ⟨T', hT', hφ⟩ := h Set.univ (Set.subset_univ _)
  rwa [Set.eq_univ_of_univ_subset hT'] at hφ

/-- A jewel with a prescribed tag: `{J, t}` with `J ∈ J`. -/
noncomputable def jewelOf (t : HSet.{u}) : HSet.{u} :=
  decorateWith (fun _ _ : PUnit.{u + 1} => True) (fun _ => t) PUnit.unit

theorem mem_jewelOf {t y : HSet.{u}} : y ∈ jewelOf t ↔ y = jewelOf t ∨ y = t := by
  unfold jewelOf
  rw [mem_decorateWith]
  constructor
  · rintro (⟨_, _, rfl⟩ | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨PUnit.unit, trivial, rfl⟩
    · exact Or.inr rfl

theorem jewelOf_mem_self (t : HSet.{u}) : jewelOf t ∈ jewelOf t :=
  mem_jewelOf.mpr (Or.inl rfl)

theorem below_jewelOf {t z : HSet.{u}} (h : Below (jewelOf t) z) :
    z = jewelOf t ∨ Below t z := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hmem ih =>
    rcases ih with rfl | below
    · rcases mem_jewelOf.mp hmem with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr .refl
    · exact Or.inr (below.tail hmem)

/-- **Under cofinally many inaccessibles, every closed stage has a closed extension that is
no `B_ν`.** Above a stage of height `κ`, take an inaccessible `μ > κ` and the jewel tagged by
the ordinal `κ`, and separate `B_μ` so as to keep the old stage and drop the jewel. -/
theorem exists_extension_not_branching (h : CofinalInaccessibles.{u}) {A : HSet.{u}}
    (hA : HClosed A) : ∃ B : HSet.{u}, HClosed B ∧ A ⊆ B ∧ ∀ ν : Cardinal.{u}, B ≠ branching ν := by
  obtain ⟨κ, _, hAκ, hω⟩ := exists_branching_above hA
  obtain ⟨μ, hμ, above⟩ := h κ.ord
  have hκμ : κ < μ := ord_lt_ord.mp above
  let t : HSet.{u} := HSet.ofZFSet κ.ord.toZFSet
  have notInA : jewelOf t ∉ A := by
    intro hJ
    have member : t ∈ branching κ :=
      HSet.subset_iff.mp hAκ (hA.transitive hJ (mem_jewelOf.mpr (Or.inr rfl)))
    have fewer := smallMembers_ofZFSet_iff.mp (mem_branching.mp member).smallMembers
    rw [Ordinal.card_toZFSet, card_ord] at fewer
    exact lt_irrefl _ fewer
  have inμ : jewelOf t ∈ branching μ := by
    refine mem_branching.mpr fun z hz => ?_
    rcases below_jewelOf hz with rfl | below
    · refine ⟨ULift.{u} Bool, fun b => if b.down then jewelOf t else t,
        (lt_aleph0_of_finite _).trans hμ.aleph0_lt, fun y => ?_⟩
      rw [mem_jewelOf]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨⟨true⟩, rfl⟩
        · exact ⟨⟨false⟩, rfl⟩
      · rintro ⟨⟨b⟩, rfl⟩
        cases b
        · exact Or.inr rfl
        · exact Or.inl rfl
    · exact herSmall_ofZFSet_toZFSet (by rw [card_ord]; exact hκμ) z below
  have hBμ : HClosed (branching μ) := hclosed_branching_iff.mpr (Or.inr (Or.inr hμ))
  let E : HSet.{u} → Prop := fun w => w ∈ A
  have hE : ∀ ⦃x : HSet.{u}⦄, E x → ∀ ⦃y : HSet.{u}⦄, y ∈ x → E y ∨ y.WF :=
    fun x hx y hy => Or.inl (hA.transitive hx hy)
  let B := HSet.sep (AccExcept E) (branching μ)
  have hB : HClosed B := hBμ.sep_stable (stable_accExcept hE)
  refine ⟨B, hB, HSet.subset_iff.mpr fun x hx => HSet.mem_sep.mpr
    ⟨HSet.subset_iff.mp (branching_mono hκμ.le) (HSet.subset_iff.mp hAκ hx),
      accExcept_of_mem hx⟩, fun ν equal => ?_⟩
  have heights : V_ μ.ord = V_ ν.ord := by
    have left : HSet.toZFSet B = V_ μ.ord := by
      have hwf : ∀ x : HSet.{u}, x.WF → AccExcept E x := fun x hx =>
        Subrelation.accessible (q := fun z w : HSet.{u} => z ∈ w ∧ ¬ E w) (fun h => h.1) hx
      show HSet.toZFSet (HSet.sep (AccExcept E) (branching μ)) = _
      rw [toZFSet_sep_of_wf hwf, toZFSet_branching hBμ]
    rw [← left, equal, toZFSet_branching (equal ▸ hB)]
  have same : μ = ν := by
    have ranks := congrArg ZFSet.rank heights
    rw [ZFSet.rank_vonNeumann, ZFSet.rank_vonNeumann] at ranks
    exact ord_injective ranks
  subst same
  have member : jewelOf t ∈ B := equal ▸ inμ
  exact not_acc_of_rel_self (r := fun z w : HSet.{u} => z ∈ w ∧ ¬ E w)
    ⟨jewelOf_mem_self t, notInA⟩ (HSet.mem_sep.mp member).2

/-- **Under cofinally many inaccessibles, the closed stages refute `.1`**, for the valuation
"the stage is some `B_ν`". -/
theorem not_valid_dot1_hclosed (h : CofinalInaccessibles.{u}) :
    ¬ Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) (axiomDot1 (.atom 0)) := by
  intro hvalid
  let val : ℕ → {U : HSet.{u} // HClosed U} → Prop := fun _ W => ∃ ν, W.1 = branching ν
  have forced := hvalid val ⟨∅, hclosed_empty⟩
  simp only [axiomDot1, forces_impl, forces_box, forces_diamond, forces_atom] at forced
  obtain ⟨A, _, hbox⟩ := forced fun A _ => by
    obtain ⟨ν, hν, hAν, _⟩ := exists_branching_above A.2
    exact ⟨⟨branching ν, hν⟩, hAν, ν, rfl⟩
  obtain ⟨B, hB, hAB, notB⟩ := exists_extension_not_branching h A.2
  obtain ⟨ν, hν⟩ := hbox ⟨B, hB⟩ hAB
  exact notB ν hν

/-- **The logic of the closed stages is strictly smaller than the logic of the finite Boolean
algebras**, under cofinally many inaccessibles: `.1` separates them. -/
theorem dot1_separates_stages_from_powersets (h : CofinalInaccessibles.{u}) :
    (∀ n, Valid (fun S T : Set (Fin n) => S ⊆ T) (axiomDot1 (.atom 0))) ∧
      ¬ Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) (axiomDot1 (.atom 0)) :=
  ⟨fun n => valid_dot1_powerset n _, not_valid_dot1_hclosed h⟩

#print axioms not_valid_dot1_hclosed
#print axioms jewel_injective
#print axioms exists_stage_with_jewels
#print axioms stage_onto_powerset
#print axioms valid_powerset_of_valid_hclosed

end Mettapedia.SetTheory.OpenTower.AntiFounded
