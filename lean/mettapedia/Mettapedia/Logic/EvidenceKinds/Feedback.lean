import Mettapedia.Logic.EvidenceKinds.Beliefs
import Mettapedia.GSLT.Causality.SemiringFactStores
import Provenance.Semirings.Why
import Provenance.Semirings.Which

/-!
# Provenance through rules: lineage, why-provenance, and feedback

A transform's output rests on what it read, and a rule run under a declared mode adds the mode's
own mark. Annotating a fact store in a provenance semiring (`SemiringFactStores`) makes this a
computation: a firing contributes its weight times the product of its reads' annotations, and the
contributions to one fact add up. Two provenance semirings matter here (Green, Karvounarakis and
Tannen, *Provenance semirings*, PODS 2007; the instances are those of Senellart's package):

* **lineage** (`Which`): the set of atoms some derivation of a fact used;
* **why-provenance** (`Why`): the set of witnesses, each the set of atoms one derivation used.

## Why-provenance makes deletion exact on every rule set

The valuation of the atoms that survive a deletion is a semiring homomorphism from why-provenance
to presence (`survives`): a fact survives when one of its witnesses survives entirely. Since a
homomorphism commutes with every stage (`map_kStage`) and presence stages are the set closure
(`mem_saturation_iff_presence`), **a fact is derivable from the surviving seeds exactly when one of
its witnesses lies among them** (`why_deletion_exact`). No rank is needed: on the two-atom cycle,
where retraction by counting keeps both atoms alive
(`SemiringControls.counting_retraction_inexact_on_cycle`), why-provenance retracts both
(`Controls.cycle_why_retracts`). Counting is exact only on ranked rules
(`retraction_exact_of_ranked`); derivation identity, in the form of witnesses, is exact everywhere.

## Lineage makes feedback visible

* **At a fixed point, the output of a firing contains the lineage of each of its reads**
  (`lineage_read_le_output`) **and the mark of its rule** (`lineage_weight_le_output`). So a
  `whenever` rule that reads evidence and emits a conclusion never produces evidence independent of
  what it read: the stamp guard refuses revising the two (`feedback_refused`), and a trust-me
  firing's output rests on its promise (`trust_mark_in_output`).
* **Lineage and why-provenance stages stop on finite atoms** (`lineage_stages_stop`,
  `why_stages_stop`, from `kStage_eventually_fixed`).
* **Count annotation diverges on a recursive rule**: on the self-feeding rule one positive
  observation becomes `n` after `n` stages (`Controls.counts_inflate`), while its lineage is one
  atom from the first stage on (`Controls.lineage_constant`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra (Presence supportOfCount)
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.PLN.Bridges.KR.RevisionStampedWitnessBridge

universe uRule

/-! ## Why-provenance and deletion -/

section Why

variable {Var : Type}

open Classical in
/-- **The valuation of surviving atoms**: a why-annotation is present when one of its witnesses
lies among the surviving atoms. -/
noncomputable def survives (alive : Set Var) : Why Var →+* Presence where
  toFun annotation := ⟨decide (∃ witness ∈ annotation.carrier, witness ⊆ alive)⟩
  map_one' := by
    apply Presence.ext'
    show decide (∃ witness ∈ ({∅} : Set (Set Var)), witness ⊆ alive) = true
    simp
  map_mul' first second := by
    apply Presence.ext'
    show decide (∃ witness ∈ {z | ∃ x y, x ∈ first.carrier ∧ y ∈ second.carrier ∧ z = x ∪ y},
        witness ⊆ alive) =
      (decide (∃ witness ∈ first.carrier, witness ⊆ alive) &&
        decide (∃ witness ∈ second.carrier, witness ⊆ alive))
    rw [← Bool.decide_and]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨_, ⟨x, y, hx, hy, rfl⟩, sub⟩
      exact ⟨⟨x, hx, (Set.union_subset_iff.mp sub).1⟩, ⟨y, hy, (Set.union_subset_iff.mp sub).2⟩⟩
    · rintro ⟨⟨x, hx, subx⟩, ⟨y, hy, suby⟩⟩
      exact ⟨x ∪ y, ⟨x, y, hx, hy, rfl⟩, Set.union_subset subx suby⟩
  map_zero' := by
    apply Presence.ext'
    show decide (∃ witness ∈ (∅ : Set (Set Var)), witness ⊆ alive) = false
    simp
  map_add' first second := by
    apply Presence.ext'
    show decide (∃ witness ∈ first.carrier ∪ second.carrier, witness ⊆ alive) =
      (decide (∃ witness ∈ first.carrier, witness ⊆ alive) ||
        decide (∃ witness ∈ second.carrier, witness ⊆ alive))
    rw [← Bool.decide_or]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨witness, member | member, sub⟩
      · exact Or.inl ⟨witness, member, sub⟩
      · exact Or.inr ⟨witness, member, sub⟩
    · rintro (⟨witness, member, sub⟩ | ⟨witness, member, sub⟩)
      · exact ⟨witness, Or.inl member, sub⟩
      · exact ⟨witness, Or.inr member, sub⟩

theorem survives_present (alive : Set Var) (annotation : Why Var) :
    (survives alive annotation).present = true ↔ ∃ witness ∈ annotation.carrier, witness ⊆ alive := by
  classical
  show decide _ = true ↔ _
  simp

instance [Finite Var] : Finite (Why Var) :=
  Finite.of_injective Why.carrier fun _ _ same => Why.ext same

end Why

section Deletion

variable {R : Type} [DecidableEq R] (S : System.{0, uRule} R)

open Classical in
/-- **Each seed is its own atom.** -/
noncomputable def whySeed (seed : Set R) (r : R) : Why R := if r ∈ seed then ⟨{{r}}⟩ else 0

/-- **Deletion is exact with why-provenance, on every rule set**: a fact is derivable from the
surviving seeds exactly when one of its witnesses lies among the surviving atoms. -/
theorem why_deletion_exact (catalogue : List S.Entry) (seed alive : Set R) (r : R) :
    r ∈ S.saturation {entry | entry ∈ catalogue} (seed ∩ alive) ↔
      ∃ n, ∃ witness ∈ (S.kStage catalogue (whySeed seed) (fun _ => 1) n r).carrier,
        witness ⊆ alive := by
  classical
  rw [S.mem_saturation_iff_presence catalogue (seed ∩ alive) r]
  apply exists_congr
  intro n
  have seeds : (survives alive ∘ whySeed seed) =
      (supportOfCount ∘ fun r => if r ∈ seed ∩ alive then 1 else 0) := by
    funext x
    apply Presence.ext'
    by_cases inSeed : x ∈ seed
    · by_cases isAlive : x ∈ alive
      · have := (survives_present alive ⟨{{x}}⟩).mpr
          ⟨{x}, Set.mem_singleton {x}, Set.singleton_subset_iff.mpr isAlive⟩
        simpa [whySeed, inSeed, isAlive, supportOfCount] using this
      · have notPresent : ¬ (survives alive ⟨{{x}}⟩).present = true := by
          rw [survives_present]
          rintro ⟨witness, member, sub⟩
          rw [Set.mem_singleton_iff.mp member] at sub
          exact isAlive (sub (Set.mem_singleton x))
        simp only [Bool.not_eq_true] at notPresent
        simpa [whySeed, inSeed, isAlive, supportOfCount] using notPresent
    · simp [whySeed, inSeed, supportOfCount]
  have weights : (survives alive ∘ fun _ : S.Entry => (1 : Why R)) =
      (supportOfCount ∘ fun _ : S.Entry => 1) := by
    funext x
    simp
  have mapped := congrFun (S.map_kStage (survives alive) catalogue (whySeed seed) (fun _ => 1) n) r
  rw [← survives_present, mapped, seeds, weights]
  convert Iff.rfl

/-- Why-provenance stages stop on finitely many facts. -/
theorem why_stages_stop [Finite R] (catalogue : List S.Entry) (seed : R → Why R)
    (weight : S.Entry → Why R) :
    ∃ N, (∀ n, N ≤ n → S.kStage catalogue seed weight n = S.kStage catalogue seed weight N) ∧
      S.kStep catalogue seed weight (S.kStage catalogue seed weight N) =
        S.kStage catalogue seed weight N :=
  S.kStage_eventually_fixed catalogue seed weight

end Deletion

/-! ## Lineage and feedback -/

section Lineage

variable {Var : Type} [DecidableEq Var]

/-- The atoms of a lineage annotation. -/
def lineageSet : Which Var → Finset Var
  | .wset atoms => atoms
  | .wbot => ∅

instance [Fintype Var] : Finite (Which Var) :=
  Finite.of_injective (fun annotation : Which Var => match annotation with
    | .wset atoms => some atoms
    | .wbot => none) (by
      intro first second same
      cases first <;> cases second <;> simp_all)

theorem which_mul_wset (first second : Finset Var) :
    (Which.wset first * Which.wset second : Which Var) = Which.wset (first ∪ second) := rfl

omit [DecidableEq Var] in
theorem which_le_wset {first second : Finset Var} :
    (Which.wset first : Which Var) ≤ Which.wset second ↔ first ⊆ second := Iff.rfl

omit [DecidableEq Var] in
theorem which_ne_zero {annotation : Which Var} :
    annotation ≠ 0 ↔ ∃ atoms, annotation = Which.wset atoms := by
  cases annotation with
  | wset atoms => exact ⟨fun _ => ⟨atoms, rfl⟩, fun _ => by intro h; cases h⟩
  | wbot => exact ⟨fun h => absurd rfl h, fun ⟨_, h⟩ => by cases h⟩

/-- **In lineage, a nonzero product contains each nonzero factor.** -/
theorem which_le_mul {first second : Which Var} (nonzero : first * second ≠ 0) :
    first ≤ first * second := by
  cases first with
  | wbot => exact absurd rfl nonzero
  | wset atoms =>
      cases second with
      | wbot => exact absurd rfl nonzero
      | wset others => exact which_le_wset.mpr Finset.subset_union_left

omit [DecidableEq Var] in
theorem lineageSet_mono {first second : Which Var} (le : first ≤ second) :
    lineageSet first ⊆ lineageSet second := by
  cases first with
  | wbot => simp [lineageSet]
  | wset atoms =>
      cases second with
      | wbot => exact absurd le id
      | wset others => exact le

variable {R : Type} [DecidableEq R] (S : System.{0, uRule} R)

/-- A firing's contribution lies below the annotation of everything it produces, at a fixed point. -/
theorem firing_le_output (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) {f : R → Which Var}
    (fixed : S.kStep catalogue seed weight f = f) {entry : S.Entry} (member : entry ∈ catalogue)
    {b : R} (produces : b ∈ S.produce entry.2) : S.firingValue weight f entry ≤ f b := by
  have unfolded : f b = seed b + (catalogue.map fun entry =>
      ((S.produce entry.2).count b : Which Var) * S.firingValue weight f entry).sum := by
    conv_lhs => rw [← fixed]
    rfl
  rw [unfolded]
  have count : 1 ≤ (S.produce entry.2).count b := Multiset.count_pos.mpr produces
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le count
  have term : S.firingValue weight f entry ≤
      ((S.produce entry.2).count b : Which Var) * S.firingValue weight f entry := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_self_add
  refine term.trans (le_add_left (List.le_sum_of_mem ?_))
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- **At a fixed point, the output of a firing contains the lineage of each of its reads.** -/
theorem lineage_read_le_output (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) {f : R → Which Var}
    (fixed : S.kStep catalogue seed weight f = f) {entry : S.Entry} (member : entry ∈ catalogue)
    {a b : R} (reads : a ∈ S.read entry.2) (produces : b ∈ S.produce entry.2)
    (fires : S.firingValue weight f entry ≠ 0) : f a ≤ f b := by
  refine le_trans ?_ (firing_le_output S catalogue seed weight fixed member produces)
  have split : ((S.read entry.2).map f).prod = f a * (((S.read entry.2).erase a).map f).prod := by
    conv_lhs => rw [← Multiset.cons_erase reads]
    rw [Multiset.map_cons, Multiset.prod_cons]
  unfold System.firingValue at fires ⊢
  rw [split] at fires ⊢
  have rearranged : weight entry * (f a * (((S.read entry.2).erase a).map f).prod) =
      f a * (weight entry * (((S.read entry.2).erase a).map f).prod) := by ring
  rw [rearranged] at fires ⊢
  exact which_le_mul fires

/-- **At a fixed point, the output of a firing contains the mark of its rule.** -/
theorem lineage_weight_le_output (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) {f : R → Which Var}
    (fixed : S.kStep catalogue seed weight f = f) {entry : S.Entry} (member : entry ∈ catalogue)
    {b : R} (produces : b ∈ S.produce entry.2)
    (fires : S.firingValue weight f entry ≠ 0) : weight entry ≤ f b :=
  (which_le_mul fires).trans (firing_le_output S catalogue seed weight fixed member produces)

/-- **A trust-me firing's output rests on its promise.** -/
theorem trust_mark_in_output (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) {f : R → Which Var}
    (fixed : S.kStep catalogue seed weight f = f) {entry : S.Entry} (member : entry ∈ catalogue)
    {b : R} (produces : b ∈ S.produce entry.2) (fires : S.firingValue weight f entry ≠ 0)
    {promise : Var} (marked : promise ∈ lineageSet (weight entry)) :
    promise ∈ lineageSet (f b) :=
  lineageSet_mono (lineage_weight_le_output S catalogue seed weight fixed member produces fires) marked

/-- The packet of a fact: its evidence, stamped with its lineage. -/
def factPacket (evidence : Mettapedia.PLN.Evidence.BinaryEvidence) (annotation : Which Var) :
    StampedBinaryEvidence Var :=
  ⟨evidence, lineageSet annotation⟩

/-- **Feedback is refused**: a `whenever` rule's output cannot be revised with what it read, when
what it read rests on some atom. -/
theorem feedback_refused (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) {f : R → Which Var}
    (fixed : S.kStep catalogue seed weight f = f) {entry : S.Entry} (member : entry ∈ catalogue)
    {a b : R} (reads : a ∈ S.read entry.2) (produces : b ∈ S.produce entry.2)
    (fires : S.firingValue weight f entry ≠ 0) {atom : Var} (rests : atom ∈ lineageSet (f a))
    (readEvidence outputEvidence : Mettapedia.PLN.Evidence.BinaryEvidence) :
    guardedRevisionManyEvidence [factPacket readEvidence (f a), factPacket outputEvidence (f b)] =
      none :=
  guardedRevisionManyEvidence_pair_rejects_shared_stamp rests
    (lineageSet_mono (lineage_read_le_output S catalogue seed weight fixed member reads produces fires)
      rests)

/-- Lineage stages stop on finitely many facts and atoms. -/
theorem lineage_stages_stop [Fintype Var] [Finite R] (catalogue : List S.Entry) (seed : R → Which Var)
    (weight : S.Entry → Which Var) :
    ∃ N, (∀ n, N ≤ n → S.kStage catalogue seed weight n = S.kStage catalogue seed weight N) ∧
      S.kStep catalogue seed weight (S.kStage catalogue seed weight N) =
        S.kStage catalogue seed weight N :=
  S.kStage_eventually_fixed catalogue seed weight

end Lineage

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.Causality.ResourceInteraction.SemiringControls
open Mettapedia.PLN.WorldModel.EvidenceSpaces

/-- **Count annotation inflates on a recursive rule**: one positive observation fed back through
the self-feeding rule counts `n` after `n` stages. -/
theorem counts_inflate (n : ℕ) :
    selfFeeding.kStage selfCatalogue (fun _ => (1 : Evidence ℕ)) (fun _ => 1) n () = ⟨n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [System.kStage_succ, selfFeeding_kStep, ih, one_mul]
      ext <;> simp [add_comm]

/-- **Lineage is one atom from the first stage on.** -/
theorem lineage_constant (n : ℕ) :
    selfFeeding.kStage selfCatalogue (fun _ => (Which.wset {()} : Which Unit)) (fun _ => 1) (n + 1) () =
      Which.wset {()} := by
  induction n with
  | zero =>
      rw [System.kStage_succ, selfFeeding_kStep, System.kStage_zero, one_mul]
      rfl
  | succ n ih =>
      rw [System.kStage_succ, selfFeeding_kStep, ih, one_mul]
      show Which.wset ({()} ∪ {()}) = Which.wset {()}
      rw [Finset.union_idempotent]

/-- **On the cycle, why-provenance retracts both atoms**: with seed `true`, both atoms are derived;
after `true` is retracted, no witness of either survives, while retraction by counting keeps both
alive (`counting_retraction_inexact_on_cycle`). -/
theorem cycle_why_retracts :
    (∀ b, ∃ n, ∃ witness ∈ (cycle.kStage cycleCatalogue (whySeed {true}) (fun _ => 1) n b).carrier,
        witness ⊆ Set.univ) ∧
      (∀ b n, ∀ witness ∈ (cycle.kStage cycleCatalogue (whySeed {true}) (fun _ => 1) n b).carrier,
        ¬ witness ⊆ {false}) := by
  have retracted : cycle.saturation {entry | entry ∈ cycleCatalogue} ({true} ∩ {false}) = ∅ := by
    have empty : ({true} ∩ {false} : Set Bool) = ∅ := by
      ext b; cases b <;> simp
    rw [empty]
    exact counting_retraction_inexact_on_cycle.2.2
  refine ⟨fun b => ?_, fun b n witness member sub => ?_⟩
  · rw [← why_deletion_exact, Set.inter_univ]
    have least := cycle.saturation_isLeast {entry | entry ∈ cycleCatalogue} {true}
    have trueIn : true ∈ cycle.saturation {entry | entry ∈ cycleCatalogue} {true} :=
      least.1.1 rfl
    cases b
    · refine least.1.2 ⟨⟨(), false⟩, by simp [cycleCatalogue]⟩ ⟨fun a inRead => ?_, by simp [cycle]⟩
      have : a = true := by simpa [cycle] using inRead
      subst this
      exact trueIn
    · exact trueIn
  · have derivable := (why_deletion_exact cycle cycleCatalogue {true} {false} b).mpr
      ⟨n, witness, member, sub⟩
    rw [retracted] at derivable
    exact derivable

end Controls

end Mettapedia.Logic.EvidenceKinds
