import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# Spaces of samples and the algebra of evidence

A space can be read as a bag of samples of a world state.  The evidence a bag
gives a proposition is the pair of counts `(n⁺, n⁻)` of samples where it holds
and fails (`ofSamples`).  Everything below is derived from that reading.

## Revision and conjunction are derived

* **Revision is addition** (`ofSamples_add`): pooling two bags of samples adds
  their counts.  So a bag of samples with this extraction is an additive world
  model (`sampleWorldModel`), and every rewrite of the world-model calculus
  preserves the evidence it extracts (`samples_calculus_sound`).
* **Conjunction over paired samples** (`ofSamples_product`): the evidence for
  `φ ∧ ψ` over every pair of a sample of `φ` and a sample of `ψ` is
  `(a⁺b⁺, a⁺b⁻ + a⁻b⁺ + a⁻b⁻)`.  With coordinatewise addition this product
  makes `Evidence R` a commutative semiring over any commutative semiring `R`,
  with unit `(1, 0)`, one positive sample.  Pairing is bilinear, which is the
  cross-term law that additive counting of pairs lacks.
* **Both are forced** (`revision_unique`, `conjunction_unique`): every count
  pair is the evidence of some bag of samples (`ofSamples_surjective`), so an
  operation on counts that agrees with pooling, or with pairing, is addition,
  or the paired product.

Pairing here means the Cartesian product of two sample bags. Conjunction of
two predicates on the same observed world retains their joint correlation;
their two marginal count pairs do not determine it
(`no_same_world_conjunction_from_marginals`). Thus the paired product is not
a universal replacement for world-model inference or dependent evidence.

So evidence is an annotation algebra in the sense of
`Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra`: spaces and answers can be
annotated by `Evidence ℕ`, alternatives revise by addition and sequencing
conjoins by the paired product.

## Readouts

* The positive count and the total count are semiring homomorphisms
  (`posHom`, `totalHom`), hence monad morphisms of evidence-weighted answers
  (`Ans.mapK_bind`).  Under them `Evidence R` is the semiring of pairs
  `(positive, total)`.
* **Strength** `n⁺ / (n⁺ + n⁻)` is multiplicative over conjunction
  (`strength_mul`) and is the mediant of the two strengths under revision
  (`strength_add`).  With no samples it is undetermined (`readout`):
  "nothing known yet, so ask".
* Evidence counts have no zero divisors (`instNoZeroDivisors`), so possibility
  composes for evidence-weighted answers (`support_bind_evidence`).  The
  coordinatewise product of PLN's binary evidence has one
  (`binary_tensor_zero_divisor`) and is not the paired-sample conjunction
  (`binary_tensor_ne_paired`), although both share revision
  (`toPaired_add`).

## Capabilities

* revision: addition only;
* conjunction and bind: the commutative semiring;
* retraction of a known batch: truncated subtraction, which undoes revision
  for counts (`retract_revision`) and distributes over conjunction when the
  retracted batch is part of the evidence (`conj_retract_of_le`), but not in
  general (`conj_retract_fails`): retraction needs to know what was revised;
* merging copies that may overlap: the coordinatewise maximum, idempotent but
  not additive;
* strength: division, partial at zero.

## Revision without coordination

Additive revision double counts a copy delivered twice
(`additive_merge_double_counts`).  Keyed by source, with each source's
cumulative evidence merged by maximum and the readout summing over sources,
revision tolerates duplicated and reordered delivery
(`sourceMerge_idempotent`, `sourceMerge_comm`) and counts each source's
latest evidence once (`readout_sourceMerge`): the grow-only counter of
replicated data types, here for evidence.

## Conditioning

Conditioning a bag of samples on an observed event keeps the samples where it
holds.  It commutes with revision (`condition_add`), and the positive count of
`φ` given `E` is the positive count of `E` given `φ`
(`condition_pos_symm`): Bayes' rule in counts.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.EvidenceSpaces

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

universe u v

/-- Positive and negative counts. -/
@[ext] structure Evidence (R : Type u) where
  /-- Samples where the proposition holds. -/
  pos : R
  /-- Samples where it fails. -/
  neg : R

namespace Evidence

section Algebra

variable {R : Type u} [CommSemiring R]

instance : Zero (Evidence R) := ⟨⟨0, 0⟩⟩
instance : One (Evidence R) := ⟨⟨1, 0⟩⟩
instance : Add (Evidence R) := ⟨fun a b => ⟨a.pos + b.pos, a.neg + b.neg⟩⟩

/-- **Conjunction over paired samples.** -/
instance : Mul (Evidence R) :=
  ⟨fun a b => ⟨a.pos * b.pos, a.pos * b.neg + a.neg * b.pos + a.neg * b.neg⟩⟩

@[simp] theorem zero_pos : (0 : Evidence R).pos = 0 := rfl
@[simp] theorem zero_neg : (0 : Evidence R).neg = 0 := rfl
@[simp] theorem one_pos : (1 : Evidence R).pos = 1 := rfl
@[simp] theorem one_neg : (1 : Evidence R).neg = 0 := rfl
@[simp] theorem add_pos (a b : Evidence R) : (a + b).pos = a.pos + b.pos := rfl
@[simp] theorem add_neg (a b : Evidence R) : (a + b).neg = a.neg + b.neg := rfl
@[simp] theorem mul_pos (a b : Evidence R) : (a * b).pos = a.pos * b.pos := rfl
@[simp] theorem mul_neg (a b : Evidence R) :
    (a * b).neg = a.pos * b.neg + a.neg * b.pos + a.neg * b.neg := rfl

instance : CommSemiring (Evidence R) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  npow := npowRec

/-- The total number of samples. -/
def total (e : Evidence R) : R := e.pos + e.neg

/-- The positive count is a semiring homomorphism. -/
def posHom : Evidence R →+* R where
  toFun := pos
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The total count is a semiring homomorphism. -/
def totalHom : Evidence R →+* R where
  toFun := total
  map_one' := by simp [total]
  map_mul' a b := by simp [total]; ring
  map_zero' := by simp [total]
  map_add' a b := by simp [total]; ring

@[simp] theorem totalHom_apply (e : Evidence R) : totalHom e = e.pos + e.neg := rfl

@[simp] theorem total_mul (a b : Evidence R) : (a * b).total = a.total * b.total :=
  totalHom.map_mul a b

@[simp] theorem total_add (a b : Evidence R) : (a + b).total = a.total + b.total :=
  totalHom.map_add a b

/-- One positive sample. -/
def positive : Evidence R := ⟨1, 0⟩

/-- One negative sample. -/
def negative : Evidence R := ⟨0, 1⟩

theorem positive_eq_one : (positive : Evidence R) = 1 := rfl

theorem negative_mul (e : Evidence R) : negative * e = ⟨0, e.total⟩ := by
  ext <;> simp [negative, total]

end Algebra

/-! ### Order and zero divisors -/

section Order

variable {R : Type u} [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

instance : PartialOrder (Evidence R) where
  le a b := a.pos ≤ b.pos ∧ a.neg ≤ b.neg
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ first second := ⟨first.1.trans second.1, first.2.trans second.2⟩
  le_antisymm a b first second := Evidence.ext (le_antisymm first.1 second.1)
    (le_antisymm first.2 second.2)

omit [CommSemiring R] [CanonicallyOrderedAdd R] in
theorem le_def (a b : Evidence R) : a ≤ b ↔ a.pos ≤ b.pos ∧ a.neg ≤ b.neg := Iff.rfl

instance : CanonicallyOrderedAdd (Evidence R) where
  exists_add_of_le {a b} le := by
    obtain ⟨p, hp⟩ := exists_add_of_le le.1
    obtain ⟨n, hn⟩ := exists_add_of_le le.2
    exact ⟨⟨p, n⟩, Evidence.ext hp hn⟩
  le_add_self a b := ⟨le_add_self, le_add_self⟩
  le_self_add a b := ⟨le_self_add, le_self_add⟩

instance instNoZeroDivisors [NoZeroDivisors R] : NoZeroDivisors (Evidence R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} product := by
    have pos : a.pos * b.pos = 0 := congrArg Evidence.pos product
    have neg : a.pos * b.neg + a.neg * b.pos + a.neg * b.neg = 0 :=
      congrArg Evidence.neg product
    rw [add_eq_zero, add_eq_zero] at neg
    obtain ⟨⟨pn, np⟩, nn⟩ := neg
    by_cases aPos : a.pos = 0
    · by_cases aNeg : a.neg = 0
      · exact Or.inl (Evidence.ext aPos aNeg)
      · right
        exact Evidence.ext ((mul_eq_zero.1 np).resolve_left aNeg)
          ((mul_eq_zero.1 nn).resolve_left aNeg)
    · right
      exact Evidence.ext ((mul_eq_zero.1 pos).resolve_left aPos)
        ((mul_eq_zero.1 pn).resolve_left aPos)

end Order

/-! ### Change of count semiring -/

section Map

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-- Evidence is functorial in the count semiring: a semiring map acts on both
counts and preserves revision and paired conjunction. -/
def map (f : R →+* S) : Evidence R →+* Evidence S where
  toFun e := ⟨f e.pos, f e.neg⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

@[simp] theorem map_apply_pos (f : R →+* S) (e : Evidence R) : (map f e).pos = f e.pos := rfl

@[simp] theorem map_apply_neg (f : R →+* S) (e : Evidence R) : (map f e).neg = f e.neg := rfl

end Map

/-! ### Strength -/

section Strength

variable {R : Type u} [Semifield R]

/-- Strength: the fraction of samples where the proposition holds. -/
def strength (e : Evidence R) : R := e.pos / e.total

/-- **Strength is multiplicative over conjunction.** -/
theorem strength_mul (a b : Evidence R) : strength (a * b) = strength a * strength b := by
  rw [strength, strength, strength, total_mul, Evidence.mul_pos, mul_div_mul_comm]

/-- **Strength of a revision is the mediant**: weighted by the sample counts. -/
theorem strength_add (a b : Evidence R) (ha : a.total ≠ 0) (hb : b.total ≠ 0)
    (hab : a.total + b.total ≠ 0) :
    strength (a + b) * (a.total + b.total) = strength a * a.total + strength b * b.total := by
  rw [strength, strength, strength, total_add, div_mul_cancel₀ _ hab, div_mul_cancel₀ _ ha,
    div_mul_cancel₀ _ hb, Evidence.add_pos]

/-- The three-valued readout: undetermined with no samples. -/
def readout [DecidableEq R] (e : Evidence R) : Option R :=
  if e.total = 0 then none else some (strength e)

theorem readout_zero [DecidableEq R] : readout (0 : Evidence R) = none := by
  simp [readout, total]

end Strength

/-! ### Retraction -/

/-- Truncated subtraction of counts. -/
instance : Sub (Evidence ℕ) := ⟨fun a b => ⟨a.pos - b.pos, a.neg - b.neg⟩⟩

/-- **Retracting a known batch undoes its revision.** -/
theorem retract_revision (a b : Evidence ℕ) : (a + b) - b = a := by
  ext
  · exact Nat.add_sub_cancel a.pos b.pos
  · exact Nat.add_sub_cancel a.neg b.neg

/-- **Retracting a batch that was revised distributes over conjunction.** -/
theorem conj_retract_of_le (a b c : Evidence ℕ) (le : c.pos ≤ b.pos ∧ c.neg ≤ b.neg) :
    a * (b - c) = a * b - a * c := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le le.1
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le le.2
  have bEq : b = c + ⟨p, n⟩ := Evidence.ext hp hn
  rw [bEq, show c + ⟨p, n⟩ - c = ⟨p, n⟩ by
    ext
    · exact Nat.add_sub_cancel_left _ _
    · exact Nat.add_sub_cancel_left _ _, mul_add, retract_revision']
where
  retract_revision' {x y : Evidence ℕ} : x + y - x = y := by
    ext
    · exact Nat.add_sub_cancel_left _ _
    · exact Nat.add_sub_cancel_left _ _

/-- **Retraction does not distribute over conjunction in general**: retracting
a positive sample that was never revised in. -/
theorem conj_retract_fails :
    (⟨0, 1⟩ : Evidence ℕ) * ((⟨0, 2⟩ : Evidence ℕ) - ⟨1, 0⟩) ≠
      (⟨0, 1⟩ : Evidence ℕ) * ⟨0, 2⟩ - (⟨0, 1⟩ : Evidence ℕ) * ⟨1, 0⟩ := by
  intro same
  have := congrArg Evidence.neg same
  revert this
  decide

end Evidence

open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence

/-! ## Evidence-weighted answers -/

/-- **Possibility composes** for answers weighted by evidence counts. -/
theorem support_bind_evidence {X Y : Type*} [DecidableEq Y] (A : Ans (Evidence ℕ) X)
    (f : X → Ans (Evidence ℕ) Y) :
    (Ans.bind A f).support = A.support.biUnion fun x => (f x).support :=
  Ans.support_bind A f

/-- The positive-count readout of an evidence-weighted bind. -/
theorem posHom_bind {X Y : Type*} (A : Ans (Evidence ℕ) X) (f : X → Ans (Evidence ℕ) Y) :
    Ans.mapK posHom (Ans.bind A f) = Ans.bind (Ans.mapK posHom A) fun x => Ans.mapK posHom (f x) :=
  Ans.mapK_bind posHom A f

/-! ## PLN's binary evidence -/

section Binary

open scoped ENNReal
open Mettapedia.PLN.Evidence

/-- Read binary evidence as counts. -/
def toPaired (e : BinaryEvidence) : Evidence ℝ≥0∞ := ⟨e.pos, e.neg⟩

/-- Revision agrees. -/
theorem toPaired_add (a b : BinaryEvidence) : toPaired (a + b) = toPaired a + toPaired b := rfl

/-- **The coordinatewise tensor has a zero divisor.** -/
theorem binary_tensor_zero_divisor :
    (⟨1, 0⟩ : BinaryEvidence) * ⟨0, 1⟩ = ⟨0, 0⟩ := by
  rw [BinaryEvidence.tensor_def]
  simp

/-- **The coordinatewise tensor is not the paired-sample conjunction**: one
sample each way, paired, gives four pairs, three of them negative. -/
theorem binary_tensor_ne_paired :
    toPaired ((⟨1, 1⟩ : BinaryEvidence) * ⟨1, 1⟩) ≠ toPaired ⟨1, 1⟩ * toPaired ⟨1, 1⟩ := by
  intro same
  have := congrArg Evidence.neg same
  simp only [toPaired, BinaryEvidence.tensor_def, mul_one, Evidence.mul_neg] at this
  norm_num at this

end Binary

/-! ## Samples -/

section Samples

variable {W : Type u}

/-- The evidence one sample gives a proposition. -/
def sampleEvidence (φ : W → Bool) (w : W) : Evidence ℕ := if φ w then positive else negative

/-- **The evidence a bag of samples gives a proposition.** -/
def ofSamples (φ : W → Bool) (samples : Multiset W) : Evidence ℕ :=
  (samples.map (sampleEvidence φ)).sum

@[simp] theorem ofSamples_zero (φ : W → Bool) : ofSamples φ 0 = 0 := by simp [ofSamples]

theorem ofSamples_cons (φ : W → Bool) (w : W) (samples : Multiset W) :
    ofSamples φ (w ::ₘ samples) = sampleEvidence φ w + ofSamples φ samples := by
  simp [ofSamples]

/-- **Revision is derived**: pooling samples adds evidence. -/
theorem ofSamples_add (φ : W → Bool) (first second : Multiset W) :
    ofSamples φ (first + second) = ofSamples φ first + ofSamples φ second := by
  simp [ofSamples]

theorem ofSamples_total (φ : W → Bool) (samples : Multiset W) :
    (ofSamples φ samples).total = Multiset.card samples := by
  induction samples using Multiset.induction_on with
  | empty => simp [total]
  | cons w samples ih =>
      rw [ofSamples_cons, total_add, ih, Multiset.card_cons, add_comm]
      unfold sampleEvidence
      cases φ w <;> simp [total, positive, negative]

theorem ofSamples_pos (φ : W → Bool) (samples : Multiset W) :
    (ofSamples φ samples).pos = Multiset.countP (fun w => φ w = true) samples := by
  induction samples using Multiset.induction_on with
  | empty => simp
  | cons w samples ih =>
      rw [ofSamples_cons, Evidence.add_pos, ih, Multiset.countP_cons]
      unfold sampleEvidence
      cases φ w <;> simp [positive, negative, add_comm]

theorem ofSamples_const_false (samples : Multiset W) :
    ofSamples (fun _ => false) samples = ⟨0, Multiset.card samples⟩ := by
  induction samples using Multiset.induction_on with
  | empty => rfl
  | cons w samples ih =>
      rw [ofSamples_cons, ih]
      ext <;> simp [sampleEvidence, negative, add_comm]

/-- **Conjunction is derived**: the evidence for `φ ∧ ψ` over all pairs of
samples is the paired product of the evidence for each. -/
theorem ofSamples_product {V : Type v} (φ : W → Bool) (ψ : V → Bool) (first : Multiset W)
    (second : Multiset V) :
    ofSamples (fun pair => φ pair.1 && ψ pair.2) (first ×ˢ second) =
      ofSamples φ first * ofSamples ψ second := by
  induction first using Multiset.induction_on with
  | empty => simp
  | cons w first ih =>
      rw [Multiset.cons_product, ofSamples_add, ih, ofSamples_cons, add_mul]
      congr 1
      have mapped : ofSamples (fun pair : W × V => φ pair.1 && ψ pair.2)
          (second.map (Prod.mk w)) = ofSamples (fun v => φ w && ψ v) second := by
        simp only [ofSamples, Multiset.map_map]
        rfl
      rw [mapped]
      unfold sampleEvidence
      cases φ w
      · simp only [Bool.false_and, Bool.false_eq_true, if_false]
        rw [ofSamples_const_false, negative_mul, ofSamples_total]
      · simp only [Bool.true_and, if_true, positive_eq_one, one_mul]

/-! ### Revision and conjunction are forced -/

theorem ofSamples_replicate (φ : W → Bool) (n : ℕ) (w : W) :
    ofSamples φ (Multiset.replicate n w) = n • sampleEvidence φ w := by
  rw [ofSamples, Multiset.map_replicate, Multiset.sum_replicate]

theorem nsmul_mk (n a b : ℕ) : n • (⟨a, b⟩ : Evidence ℕ) = ⟨n * a, n * b⟩ := by
  induction n with
  | zero =>
      rw [zero_nsmul]
      ext <;> simp
  | succ n ih =>
      rw [succ_nsmul, ih]
      ext <;> simp [Nat.succ_mul]

/-- **Every count pair is the evidence of a bag of samples.** -/
theorem ofSamples_surjective (e : Evidence ℕ) :
    ofSamples (fun b : Bool => b) (Multiset.replicate e.pos true + Multiset.replicate e.neg false) =
      e := by
  rw [ofSamples_add, ofSamples_replicate, ofSamples_replicate]
  simp only [sampleEvidence, if_true, Bool.false_eq_true, if_false, positive, negative, nsmul_mk,
    mul_one, mul_zero]
  ext <;> simp

/-- **Revision is forced**: an operation on counts that agrees with pooling
samples is addition. -/
theorem revision_unique (op : Evidence ℕ → Evidence ℕ → Evidence ℕ)
    (pooled : ∀ first second : Multiset Bool, ofSamples (fun b => b) (first + second) =
      op (ofSamples (fun b => b) first) (ofSamples (fun b => b) second)) :
    op = (· + ·) := by
  funext a b
  rw [← ofSamples_surjective a, ← ofSamples_surjective b, ← pooled, ofSamples_add]

/-- **Conjunction is forced**: an operation on counts that agrees with pairing
samples is the paired product. -/
theorem conjunction_unique (op : Evidence ℕ → Evidence ℕ → Evidence ℕ)
    (paired : ∀ first second : Multiset Bool,
      ofSamples (fun pair : Bool × Bool => pair.1 && pair.2) (first ×ˢ second) =
        op (ofSamples (fun b => b) first) (ofSamples (fun b => b) second)) :
    op = (· * ·) := by
  funext a b
  rw [← ofSamples_surjective a, ← ofSamples_surjective b, ← paired]
  exact ofSamples_product (fun b => b) (fun b => b) _ _

/-- Marginals cannot determine same-world conjunction: on the same two worlds,
identical predicates and opposite predicates have the same marginal counts
but different conjunction counts. Cartesian sample pairing has a different
contract, proved in `ofSamples_product`. -/
theorem no_same_world_conjunction_from_marginals :
    ¬ ∃ op : Evidence ℕ → Evidence ℕ → Evidence ℕ,
      ∀ (samples : Multiset Bool) (φ ψ : Bool → Bool),
        ofSamples (fun world => φ world && ψ world) samples =
          op (ofSamples φ samples) (ofSamples ψ samples) := by
  rintro ⟨op, computes⟩
  have same := computes ({true, false} : Multiset Bool) id id
  have opposite := computes ({true, false} : Multiset Bool) id Bool.not
  have add_counts (a b c d : ℕ) :
      (⟨a, b⟩ : Evidence ℕ) + ⟨c, d⟩ = ⟨a + c, b + d⟩ := by
    ext <;> rfl
  have same_counts : (⟨1, 1⟩ : Evidence ℕ) = op ⟨1, 1⟩ ⟨1, 1⟩ := by
    simpa [ofSamples, sampleEvidence, positive, negative, add_counts] using same
  have opposite_counts : (⟨0, 2⟩ : Evidence ℕ) = op ⟨1, 1⟩ ⟨1, 1⟩ := by
    simpa [ofSamples, sampleEvidence, positive, negative, add_counts] using opposite
  have positives := congrArg Evidence.pos (same_counts.trans opposite_counts.symm)
  exact Nat.one_ne_zero positives

/-! ### Conditioning -/

/-- Conditioning keeps the samples where the observed event holds. -/
def condition (event : W → Bool) (samples : Multiset W) : Multiset W :=
  samples.filter fun w => event w = true

/-- **Conditioning commutes with revision.** -/
theorem condition_add (event : W → Bool) (first second : Multiset W) :
    condition event (first + second) = condition event first + condition event second :=
  Multiset.filter_add _ _ _

/-- **Bayes' rule in counts**: positive evidence for `φ` given `E` is positive
evidence for `E` given `φ`. -/
theorem condition_pos_symm (φ event : W → Bool) (samples : Multiset W) :
    (ofSamples φ (condition event samples)).pos = (ofSamples event (condition φ samples)).pos := by
  rw [ofSamples_pos, ofSamples_pos, condition, condition, Multiset.countP_filter,
    Multiset.countP_filter]
  congr 1
  funext w
  simp [and_comm]

/-- The total evidence given `E` counts the samples of `E`. -/
theorem condition_total (φ event : W → Bool) (samples : Multiset W) :
    (ofSamples φ (condition event samples)).total =
      Multiset.countP (fun w => event w = true) samples := by
  rw [ofSamples_total, condition, Multiset.countP_eq_card_filter]

end Samples

/-! ## The world-model calculus is sound for samples -/

section Calculus

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding

variable {W : Type}

/-- **A bag of samples is an additive world model.** -/
scoped instance sampleWorldModel : AdditiveWorldModel (Multiset W) (W → Bool) (Evidence ℕ) where
  extract samples φ := ofSamples φ samples
  extract_add first second φ := ofSamples_add φ first second

/-- **Every rewrite of the world-model calculus preserves the evidence a bag of
samples gives.** -/
theorem samples_calculus_sound (world : String → Multiset W) (query : String → W → Bool)
    {s : WMSort} {source target : WMTerm s} (steps : WMContextStepStar source target) :
    (additiveReading (Ev := Evidence ℕ) world query).Agree s
      ((additiveReading (Ev := Evidence ℕ) world query).denote source)
      ((additiveReading (Ev := Evidence ℕ) world query).denote target) :=
  additive_contextStepStar_agrees world query steps

end Calculus

/-! ## Revision without coordination -/

section SourceMerge

variable {Source : Type u}

/-- Per-source cumulative evidence, merged by maximum. -/
def sourceMerge (first second : Source → Evidence ℕ) : Source → Evidence ℕ :=
  fun source => ⟨max (first source).pos (second source).pos,
    max (first source).neg (second source).neg⟩

/-- The readout sums the evidence of all sources. -/
def sourceReadout [Fintype Source] (state : Source → Evidence ℕ) : Evidence ℕ :=
  ∑ source, state source

/-- **Duplicate delivery is harmless.** -/
theorem sourceMerge_idempotent (state : Source → Evidence ℕ) : sourceMerge state state = state := by
  funext source
  ext <;> simp [sourceMerge]

/-- **Reordered delivery is harmless.** -/
theorem sourceMerge_comm (first second : Source → Evidence ℕ) :
    sourceMerge first second = sourceMerge second first := by
  funext source
  ext <;> simp [sourceMerge, max_comm]

theorem sourceMerge_assoc (first second third : Source → Evidence ℕ) :
    sourceMerge (sourceMerge first second) third = sourceMerge first (sourceMerge second third) := by
  funext source
  ext <;> simp [sourceMerge, max_assoc]

/-- **Each source's latest evidence is counted once**: when every source's
evidence grows over time, merging two copies holding that source's evidence
at two times holds it at the later time. -/
theorem readout_sourceMerge [Fintype Source] (history : Source → ℕ → Evidence ℕ)
    (grows : ∀ source, Monotone (history source)) (firstTime secondTime : Source → ℕ) :
    sourceReadout (sourceMerge (fun source => history source (firstTime source))
        (fun source => history source (secondTime source))) =
      ∑ source, history source (max (firstTime source) (secondTime source)) := by
  unfold sourceReadout
  congr 1
  funext source
  rcases le_total (firstTime source) (secondTime source) with le | le
  · have := grows source le
    ext <;> simp [sourceMerge, max_eq_right le, max_eq_right this.1, max_eq_right this.2]
  · have := grows source le
    ext <;> simp [sourceMerge, max_eq_left le, max_eq_left this.1, max_eq_left this.2]

/-- **Additive merging double counts a duplicated copy.** -/
theorem additive_merge_double_counts :
    let state : Unit → Evidence ℕ := fun _ => positive
    sourceReadout (state + state) ≠ sourceReadout state ∧
      sourceReadout (sourceMerge state state) = sourceReadout state := by
  refine ⟨?_, by rw [sourceMerge_idempotent]⟩
  intro same
  have := congrArg Evidence.pos same
  simp [sourceReadout, positive] at this

end SourceMerge

end Mettapedia.PLN.WorldModel.EvidenceSpaces
