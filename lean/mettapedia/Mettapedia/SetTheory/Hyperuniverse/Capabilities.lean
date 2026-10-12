import Mettapedia.SetTheory.Hyperuniverse.Membership
import Mettapedia.TypeTheory.TarskiUniverseCapabilities
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Small.Defs
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Codes read off the closed-set limit, and the hypersets

A code is a point of the limit. It decodes to the subtype of its members.
The universal set codes the whole carrier, so the one level codes itself.
A dependent product of that carrier is not the member-subtype of any code.
No injective map carries every hyperset into the carrier.
Replacement fails: the carrier is infinite, so some subclass is not closed,
and that subclass is a functional image of the universal set.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Hyperuniverse

open Set
open Mettapedia.TypeTheory.TarskiUniverseCapabilities
open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-! ## The one-level code family -/

/-- Codes are points of the limit. A code decodes to the subtype of its members. -/
def setCode : TarskiCodeFamily.{0, 0, 0} where
  Level := PUnit
  Code := fun _ => N
  El := fun _ code => {x : N // member x code}

example : Nonempty (setCode.El PUnit.unit univSet) :=
  ⟨⟨emptySet, member_univ emptySet⟩⟩

example : IsEmpty (setCode.El PUnit.unit emptySet) :=
  ⟨fun z => member_empty z.1 z.2⟩

/-- The members of the universal set are the whole carrier. -/
def elUnivSet : setCode.El PUnit.unit univSet ≃ N where
  toFun z := z.1
  invFun z := ⟨z, member_univ z⟩
  left_inv := by
    intro z
    rfl
  right_inv := by
    intro z
    rfl

theorem codesItself : setCode.CodesItselfAt PUnit.unit :=
  ⟨univSet, ⟨elUnivSet⟩⟩

theorem not_predicativeRanks : ¬ setCode.PredicativeRanks :=
  fun h => h PUnit.unit codesItself

example : setCode.CodesItselfAt PUnit.unit := codesItself

example : ¬ setCode.PredicativeRanks := not_predicativeRanks

/-- There is no edge of levels: the family has one level. -/
def noBelow : PUnit → PUnit → Prop := fun _ _ => False

example : ¬ noBelow PUnit.unit PUnit.unit := fun h => h

/-- Cumulativity along the empty level relation holds, because it asks for nothing. -/
def cumulativeEmpty : setCode.Cumulative noBelow where
  lift := fun below _ => below.elim
  decodeLift := fun below _ => below.elim

example : Nonempty (setCode.Cumulative noBelow) := ⟨cumulativeEmpty⟩

/-! ## A two-point code, and the failure of dependent products -/

/-- The closed set whose only points are the empty set and the universal set. -/
def bitCarrier : Set N := {emptySet, univSet}

theorem bitCarrier_compact : IsCompact bitCarrier :=
  (isCompact_singleton (x := univSet)).insert emptySet

noncomputable def bitSet : N := codeOfClosed bitCarrier_compact.isClosed

theorem member_bitSet (z : N) : member z bitSet ↔ z = emptySet ∨ z = univSet := by
  simp [bitSet, bitCarrier, member_codeOfClosed, mem_insert_iff, mem_singleton_iff]

example : member univSet bitSet := (member_bitSet univSet).2 (Or.inr rfl)

example : ¬ member quine bitSet := by
  intro h
  rcases (member_bitSet quine).1 h with hq | hq
  · exact member_empty emptySet (hq ▸ (member_quine quine).2 rfl)
  · have heq : emptySet = quine :=
      (member_quine emptySet).1 (hq.symm ▸ member_univ emptySet)
    exact member_empty emptySet ((heq.trans hq) ▸ member_univ_self)

/-- The two-point code, read as a Boolean. -/
noncomputable def elBitFun (z : {z : N // member z bitSet}) : Bool :=
  @ite _ (z.1 = univSet) (Classical.propDecidable _) true false

/-- The Boolean, read back as the empty set or the universal set. -/
noncomputable def elBitInv (b : Bool) : {z : N // member z bitSet} :=
  bif b then ⟨univSet, (member_bitSet univSet).2 (Or.inr rfl)⟩
  else ⟨emptySet, (member_bitSet emptySet).2 (Or.inl rfl)⟩

example : elBitFun ⟨univSet, (member_bitSet univSet).2 (Or.inr rfl)⟩ = true := by
  rw [elBitFun, if_pos rfl]

example : elBitFun ⟨emptySet, (member_bitSet emptySet).2 (Or.inl rfl)⟩ = false := by
  have hne : emptySet ≠ univSet := by
    intro h
    exact member_empty emptySet (h ▸ member_univ_self)
  rw [elBitFun, if_neg hne]

example : (elBitInv true).1 = univSet := by
  rw [elBitInv, cond_true]

example : (elBitInv false).1 ≠ univSet := by
  rw [elBitInv, cond_false]
  intro h
  have h' : emptySet = univSet := h
  exact member_empty emptySet (h' ▸ member_univ_self)

theorem elBit_left (z : {z : N // member z bitSet}) : elBitInv (elBitFun z) = z := by
  by_cases h : z.1 = univSet
  · rw [elBitFun, if_pos h, elBitInv, cond_true]
    exact Subtype.ext h.symm
  · rw [elBitFun, if_neg h, elBitInv, cond_false]
    obtain h0 | h1 := (member_bitSet z.1).1 z.2
    · exact Subtype.ext h0.symm
    · exact absurd h1 h

theorem elBit_right (b : Bool) : elBitFun (elBitInv b) = b := by
  cases b
  · have hne : emptySet ≠ univSet := by
      intro h
      exact member_empty emptySet (h ▸ member_univ_self)
    rw [elBitInv, cond_false, elBitFun, if_neg hne]
  · rw [elBitInv, cond_true, elBitFun, if_pos rfl]

noncomputable def elBit : {z : N // member z bitSet} ≃ Bool where
  toFun := elBitFun
  invFun := elBitInv
  left_inv := elBit_left
  right_inv := elBit_right

example : elBit ⟨univSet, (member_bitSet univSet).2 (Or.inr rfl)⟩ = true := by
  change elBitFun ⟨univSet, (member_bitSet univSet).2 (Or.inr rfl)⟩ = true
  rw [elBitFun, if_pos rfl]

example : elBit ⟨emptySet, (member_bitSet emptySet).2 (Or.inl rfl)⟩ = false := by
  change elBitFun ⟨emptySet, (member_bitSet emptySet).2 (Or.inl rfl)⟩ = false
  have hne : emptySet ≠ univSet := by
    intro h
    exact member_empty emptySet (h ▸ member_univ_self)
  rw [elBitFun, if_neg hne]

/-- No code decodes to the dependent product of the carrier with a two-point type. -/
theorem not_piClosedAt : ¬ setCode.PiClosedAt PUnit.unit := by
  classical
  intro closed
  obtain ⟨product, ⟨equivalence⟩⟩ := closed univSet (fun _ => bitSet)
  let toBool : Set N → N → Bool := fun s x => decide (x ∈ s)
  have toBool_inj : Function.Injective toBool := by
    intro s t hst
    ext x
    have hx := congrFun hst x
    simpa [toBool, decide_eq_decide] using hx
  let into : Set N → N := fun s =>
    (equivalence.symm (fun z => elBit.symm (toBool s z.1))).1
  have into_inj : Function.Injective into := by
    intro s t hst
    apply toBool_inj
    funext x
    have hz : elBit.symm (toBool s x) = elBit.symm (toBool t x) := by
      have hfun :
          equivalence.symm (fun z => elBit.symm (toBool s z.1)) =
            equivalence.symm (fun z => elBit.symm (toBool t z.1)) := by
        apply Subtype.ext
        exact hst
      have happ := congrFun (equivalence.symm.injective hfun) (elUnivSet.symm x)
      have harg : (elUnivSet.symm x).1 = x := elUnivSet.right_inv x
      rw [harg] at happ
      exact happ
    exact elBit.symm.injective hz
  exact Function.cantor_injective into into_inj

example : ¬ setCode.PiClosedAt PUnit.unit := not_piClosedAt

example : setCode.CodesItselfAt PUnit.unit ∧ ¬ setCode.PiClosedAt PUnit.unit :=
  ⟨codesItself, not_piClosedAt⟩

/-! ## The hypersets do not inject -/

/-- A self-member blocks the irreflexivity hypothesis of the membership-map obstruction. -/
theorem self_member_present : ∃ q : N, member q q :=
  ⟨univSet, member_univ_self⟩

example : member univSet univSet := member_univ_self

example : ¬ (∀ q : N, ¬ member q q) := fun h => h univSet member_univ_self

/-- No injection carries the hypersets into the carrier.
The ordinals embed into the hypersets, and they do not embed into a small type. -/
theorem no_injection_from_hypersets :
    ¬ ∃ f : HSet.{0} → N, Function.Injective f := by
  rintro ⟨f, hf⟩
  exact not_injective_of_ordinal
    (f ∘ HSet.ofZFSet ∘ Ordinal.toZFSet)
    (hf.comp (HSet.ofZFSet_injective.comp Ordinal.toZFSet_injective))

/-- No membership embedding of every hyperset exists: there is not even an injection. -/
theorem not_all_hypersets_embed :
    ¬ ∃ f : HSet.{0} → N,
        Function.Injective f ∧ ∀ x y, (x ∈ y) ↔ member (f x) (f y) := by
  rintro ⟨f, hf, _⟩
  exact no_injection_from_hypersets ⟨f, hf⟩

example : ¬ ∃ f : HSet.{0} → N, Function.Injective f := no_injection_from_hypersets

example : Function.Injective (HSet.ofZFSet ∘ Ordinal.toZFSet : Ordinal.{0} → HSet.{0}) :=
  HSet.ofZFSet_injective.comp Ordinal.toZFSet_injective

/-! ## Replacement fails -/

open Mettapedia.SetTheory.Profiles

/-- Every stage is hit by the limit. -/
theorem proj_surjective (n : ℕ) : Function.Surjective (proj n) := by
  intro x
  have hx : x ∈ (fullThread.atStage (n + 1) : Set (Stage n)) := by
    change x ∈ (fullStage (n + 1) : Set (Stage n))
    rw [fullStage, TopologicalSpace.Compacts.coe_top]
    exact Set.mem_univ x
  exact ⟨threadThrough fullThread n x hx, threadThrough_proj fullThread n x hx⟩

/-- Stage `n` has more than `n` points. -/
theorem stage_card_gt (n : ℕ) : n < Fintype.card (Stage n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stage_card_succ]
    exact (n + 1).lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (Nat.succ_pos 1) (Nat.succ_le_of_lt ih))

/-- The limit is infinite. -/
theorem carrier_infinite : Infinite N :=
  not_finite_iff_infinite.mp fun hfin => by
    have : Fintype N := Fintype.ofFinite N
    have hlt := stage_card_gt (Fintype.card N)
    have hle := Fintype.card_le_of_surjective (proj (Fintype.card N)) (proj_surjective _)
    omega

example : Infinite N := carrier_infinite

example : ¬ Finite (Stage 0) → False := fun h => h (inferInstance : Finite (Stage 0))

/-- Some subclass of the carrier is not closed. -/
theorem exists_not_isClosed : ∃ s : Set N, ¬ IsClosed s := by
  by_contra h
  push Not at h
  have : DiscreteTopology N := discreteTopology_iff_forall_isClosed.mpr h
  exact (not_finite_iff_infinite.mpr carrier_infinite) finite_of_compact_of_discrete

example : ¬ IsClosed (∅ : Set N) → False := fun h => h isClosed_empty

/-- A functional image of the universal set need not be closed, so replacement fails. -/
theorem not_replacement : ¬ HasReplacement member := by
  intro rep
  obtain ⟨s, hs⟩ := exists_not_isClosed
  have hne : s.Nonempty := by
    by_contra hempty
    exact hs (Set.not_nonempty_iff_eq_empty.mp hempty ▸ isClosed_empty)
  obtain ⟨a, ha⟩ := hne
  let R : N → N → Prop := fun x y => (x ∈ s ∧ y = x) ∨ (x ∉ s ∧ y = a)
  have hfun : ∀ x, member x univSet → Functional (R x) := by
    intro x _
    by_cases hx : x ∈ s
    · refine ⟨x, Or.inl ⟨hx, rfl⟩, ?_⟩
      intro y' hy'
      rcases hy' with ⟨_, rfl⟩ | ⟨hnot, rfl⟩
      · rfl
      · exact absurd hx hnot
    · refine ⟨a, Or.inr ⟨hx, rfl⟩, ?_⟩
      intro y' hy'
      rcases hy' with ⟨hx', rfl⟩ | ⟨_, rfl⟩
      · exact absurd hx' hx
      · rfl
  obtain ⟨b, hb⟩ := rep univSet R hfun
  have himage : ∀ y, (∃ x, member x univSet ∧ R x y) ↔ y ∈ s := by
    intro y
    constructor
    · rintro ⟨x, -, hx⟩
      rcases hx with ⟨hx, rfl⟩ | ⟨_, rfl⟩
      · exact hx
      · exact ha
    · intro hy
      exact ⟨y, member_univ y, Or.inl ⟨hy, rfl⟩⟩
  have hs_eq : s = (fixedHomeo b : Set N) := by
    ext y
    exact ((hb y).trans (himage y)).symm
  exact hs (hs_eq ▸ (fixedHomeo b).isCompact'.isClosed)

example : ¬ HasReplacement member := not_replacement

example : HasPairing member := pairing_holds

/-!
`MahloReflection` takes an ordinary-subuniverse predicate and quantifies over every
family operator. The per-operator condition is `ReflectsOperator`: some subuniverse
selected by the predicate is closed on the families drawn from it.
`WholeSubuniverseClosure` is the other closure notion, through
`HasOperatorClosedSubuniverse`, which closes one whole subuniverse under an operator.
The carrier here supplies codes and membership, and neither notion is formed from them.
`SigmaClosedAt` is not settled by the product obstruction above.
-/

end Mettapedia.SetTheory.Hyperuniverse
