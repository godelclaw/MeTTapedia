import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mettapedia.PLN.WorldModel.EvidenceSpaces

/-!
# Which laws of an annotation each readout needs

Weighted answers `Ans K X = X →₀ K` form a monad over every semiring `K`
(`WeightedAnswerAlgebra.Ans.bind_assoc`).  The readouts and operations placed on
top need further laws, and this module proves which, in both directions.

## Possibility needs a positive semiring

A semiring is **positive** when a sum vanishes only if both summands do and a
product only if a factor does (Grädel and Tannen, *Semiring provenance for
first-order model checking*, Section 2.2, where positivity is equivalent to the
support map into the Booleans being a homomorphism).

* **Positivity is exactly a zero-reflecting homomorphism into presence**
  (`positive_iff_exists_hom`).
* **Possibility composes exactly over positive semirings**
  (`support_bind_iff_positive`): the support of every bind is the union of the
  supports of the continuations on the support of the first answer, for all
  answers, if and only if `K` is positive.  Sufficiency holds over every type of
  answers (`support_bind_of_positive`); necessity needs only two answers.
* Evidence counts with the paired product are positive (`positive_evidence`);
  the coordinatewise product on pairs is not (`not_positive_pair`).

## Cancellation and possibility exclude each other

* **No nontrivial ring is positive** (`not_positive_of_ring`): `1 + (-1) = 0`.
  Signed annotations retract anything exactly, as in incremental view
  maintenance, but then possibility is not compositional.  The monus of counts
  retracts only a batch known to be part of the evidence
  (`EvidenceSpaces.retract_revision`) and keeps positivity.

## Commuting binds need commuting annotations

* **If every two independent binds commute, the annotations commute**
  (`comm_of_bind_comm`).  The converse is `WeightedAnswerAlgebra.Ans.bind_comm`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.AnnotationCapabilities

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

universe u

/-- **A positive semiring.** -/
structure Positive (K : Type u) [Semiring K] : Prop where
  left_zero_of_add : ∀ a b : K, a + b = 0 → a = 0
  zero_or_zero_of_mul : ∀ a b : K, a * b = 0 → a = 0 ∨ b = 0

variable {K : Type u} [Semiring K]

theorem Positive.both_zero_of_add (positive : Positive K) {a b : K} (sum : a + b = 0) :
    a = 0 ∧ b = 0 := by
  refine ⟨positive.left_zero_of_add a b sum, ?_⟩
  have := positive.left_zero_of_add a b sum
  rw [this, zero_add] at sum
  exact sum

/-- A finite sum in a positive semiring vanishes only if every term does. -/
theorem Positive.sum_eq_zero_iff (positive : Positive K) {ι : Type*} (s : Finset ι) (f : ι → K) :
    ∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s notMem ih =>
      rw [Finset.sum_insert notMem]
      constructor
      · intro sum
        obtain ⟨first, rest⟩ := positive.both_zero_of_add sum
        intro j member
        rcases Finset.mem_insert.1 member with rfl | inS
        · exact first
        · exact ih.1 rest j inS
      · intro zero
        rw [zero i (Finset.mem_insert_self i s),
          ih.2 fun j inS => zero j (Finset.mem_insert_of_mem inS), add_zero]

/-! ## Positivity is a zero-reflecting homomorphism into presence -/

/-- The possibility of an annotation. -/
def possible [DecidableEq K] (a : K) : Presence := ⟨decide (a ≠ 0)⟩

/-- **The possibility homomorphism** of a positive semiring. -/
def possibleHom [DecidableEq K] [Nontrivial K] (positive : Positive K) : K →+* Presence where
  toFun := possible
  map_one' := by ext; simp [possible]
  map_zero' := by ext; simp [possible]
  map_add' a b := by
    ext
    simp only [possible, ne_eq, Presence.add_present]
    by_cases ha : a = 0
    · subst ha; simp
    · have : a + b ≠ 0 := fun sum => ha (positive.left_zero_of_add a b sum)
      simp [ha, this]
  map_mul' a b := by
    ext
    simp only [possible, ne_eq, Presence.mul_present]
    by_cases ha : a = 0
    · subst ha; simp
    · by_cases hb : b = 0
      · subst hb; simp
      · have : a * b ≠ 0 := fun product =>
          (positive.zero_or_zero_of_mul a b product).elim ha hb
        simp [ha, hb, this]

/-- **Positivity is exactly a zero-reflecting homomorphism into presence.** -/
theorem positive_iff_exists_hom [Nontrivial K] :
    Positive K ↔ ∃ φ : K →+* Presence, ∀ a, φ a = 0 ↔ a = 0 := by
  classical
  constructor
  · intro positive
    refine ⟨possibleHom positive, fun a => ?_⟩
    change possible a = 0 ↔ a = 0
    constructor
    · intro h
      have := congrArg Presence.present h
      simpa [possible] using this
    · intro h
      subst h
      ext
      simp [possible]
  · rintro ⟨φ, reflects⟩
    refine ⟨fun a b sum => ?_, fun a b product => ?_⟩
    · have image : φ a + φ b = 0 := by rw [← map_add, sum, map_zero]
      have : φ a = 0 := by
        ext
        have := congrArg Presence.present image
        simp only [Presence.add_present, Presence.zero_present, Bool.or_eq_false_iff] at this
        exact this.1
      exact (reflects a).1 this
    · have image : φ a * φ b = 0 := by rw [← map_mul, product, map_zero]
      have := congrArg Presence.present image
      simp only [Presence.mul_present, Presence.zero_present, Bool.and_eq_false_iff] at this
      rcases this with h | h
      · exact Or.inl ((reflects a).1 (Presence.ext' h))
      · exact Or.inr ((reflects b).1 (Presence.ext' h))

/-! ## Possibility composes exactly over positive semirings -/

/-- **Sufficiency**: over a positive semiring possibility composes as a union. -/
theorem support_bind_of_positive (positive : Positive K) {X Y : Type*} [DecidableEq Y]
    (A : Ans K X) (f : X → Ans K Y) :
    (Ans.bind A f).support = A.support.biUnion fun x => (f x).support := by
  ext y
  simp only [Finsupp.mem_support_iff, Finset.mem_biUnion, Ans.bind_apply, Finsupp.sum, ne_eq]
  rw [positive.sum_eq_zero_iff]
  simp only [not_forall, Finsupp.mem_support_iff, exists_prop]
  constructor
  · rintro ⟨x, hx, product⟩
    refine ⟨x, hx, fun zero => product ?_⟩
    rw [zero, mul_zero]
  · rintro ⟨x, hx, hf⟩
    refine ⟨x, hx, fun product => ?_⟩
    rcases positive.zero_or_zero_of_mul _ _ product with h | h
    · exact hx h
    · exact hf h

/-- **Possibility composes exactly over positive semirings.** -/
theorem support_bind_iff_positive :
    (∀ (A : Ans K Bool) (f : Bool → Ans K Unit),
      (Ans.bind A f).support = A.support.biUnion fun x => (f x).support) ↔ Positive K := by
  classical
  constructor
  · intro composes
    refine ⟨fun a b sum => ?_, fun a b product => ?_⟩
    · by_contra ha
      have one : (1 : K) ≠ 0 := fun h => ha (by rw [← one_mul a, h, zero_mul])
      have := composes (Finsupp.single true a + Finsupp.single false b) fun _ => Ans.pure ()
      have bound : Ans.bind (Finsupp.single true a + Finsupp.single false b)
          (fun _ => (Ans.pure () : Ans K Unit)) = 0 := by
        rw [Ans.add_bind, Ans.single_bind, Ans.single_bind, Ans.pure, Finsupp.smul_single,
          Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← Finsupp.single_add,
          sum, Finsupp.single_zero]
      rw [bound, Finsupp.support_zero] at this
      have member : () ∈ (Finsupp.single true a + Finsupp.single false b).support.biUnion
          fun _ => (Ans.pure () : Ans K Unit).support := by
        rw [Finset.mem_biUnion]
        refine ⟨true, ?_, ?_⟩
        · rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
            Finsupp.single_eq_of_ne (by decide), add_zero]
          exact ha
        · rw [Finsupp.mem_support_iff, Ans.pure, Finsupp.single_eq_same]
          exact one
      rw [← this] at member
      exact absurd member (Finset.notMem_empty _)
    · by_contra both
      rw [not_or] at both
      have := composes (Finsupp.single true a) fun _ => Finsupp.single () b
      rw [Ans.single_bind, Finsupp.smul_single, smul_eq_mul, product, Finsupp.single_zero,
        Finsupp.support_zero] at this
      have member : () ∈ (Finsupp.single true a).support.biUnion
          fun _ => (Finsupp.single () b : Ans K Unit).support := by
        rw [Finset.mem_biUnion]
        refine ⟨true, ?_, ?_⟩
        · rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]
          exact both.1
        · rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]
          exact both.2
      rw [← this] at member
      exact absurd member (Finset.notMem_empty _)
  · intro positive A f
    exact support_bind_of_positive positive A f

/-! ## Cancellation and possibility exclude each other -/

/-- **No nontrivial ring is positive.** -/
theorem not_positive_of_ring {R : Type u} [Ring R] [Nontrivial R] : ¬ Positive R := fun positive =>
  one_ne_zero (positive.left_zero_of_add 1 (-1) (add_neg_cancel 1))

/-! ## Commuting binds need commuting annotations -/

/-- **If every two independent binds commute, the annotations commute.** -/
theorem comm_of_bind_comm
    (commutes : ∀ (A B : Ans K Unit) (f : Unit → Unit → Ans K Unit),
      Ans.bind A (fun x => Ans.bind B (f x)) = Ans.bind B (fun y => Ans.bind A (fun x => f x y)))
    (a b : K) : a * b = b * a := by
  have := commutes (Finsupp.single () a) (Finsupp.single () b) fun _ _ => Ans.pure ()
  simp only [Ans.single_bind, Ans.pure, Finsupp.smul_single, smul_eq_mul, mul_one] at this
  have := congrArg (fun A : Ans K Unit => A ()) this
  simpa using this

/-! ## Examples -/

open Mettapedia.PLN.WorldModel.EvidenceSpaces

/-- **Evidence counts with the paired product are positive.** -/
theorem positive_evidence : Positive (Evidence ℕ) where
  left_zero_of_add a b sum := by
    have hp := congrArg Evidence.pos sum
    have hn := congrArg Evidence.neg sum
    simp only [Evidence.add_pos, Evidence.add_neg, Evidence.zero_pos, Evidence.zero_neg,
      Nat.add_eq_zero_iff] at hp hn
    exact Evidence.ext hp.1 hn.1
  zero_or_zero_of_mul a b product := mul_eq_zero.1 product

/-- **The coordinatewise product on pairs is not positive.** -/
theorem not_positive_pair : ¬ Positive (ℕ × ℕ) := fun positive => by
  rcases positive.zero_or_zero_of_mul (1, 0) (0, 1) rfl with h | h
  · exact absurd (congrArg Prod.fst h) (by decide)
  · exact absurd (congrArg Prod.snd h) (by decide)

/-- Counts are positive. -/
theorem positive_nat : Positive ℕ where
  left_zero_of_add a b sum := by omega
  zero_or_zero_of_mul a b product := Nat.mul_eq_zero.1 product

end Mettapedia.Languages.MeTTa.AnnotationCapabilities
