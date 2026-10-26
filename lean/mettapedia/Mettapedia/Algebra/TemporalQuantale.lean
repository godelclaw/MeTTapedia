import Mettapedia.Algebra.FootprintQuantale
import Mathlib.Algebra.Group.Basic

/-!
# Reversible transport in quantale-valued temporal logic

A temporal quantale carries an additive group action by multiplicative order
isomorphisms. Residuation transports along these isomorphisms, so temporal
implications compose with the corresponding shifts. Multiplication is the
selected quantale product; probabilistic interpretations require separate
semantic premises.

The timestamped-footprint model reads a footprint at `stamp + shift`. It is a
genuine reindexing action, unlike the identity action supplied as a static
special case. Reversible reindexing and irreversible confidence decay have
different laws. In particular, ordering strength-confidence pairs solely by
strength does not define a partial order on those pairs.
-/

open Mettapedia.Algebra.QuantaleWeakness

universe u v
variable {Q : Type u} {T : Type v}

/-- An additive time action preserving multiplication and arbitrary suprema.
Bottom and top fields are retained for the authored interface. -/
class TemporalQuantale (Q : Type u) (T : Type v)
    [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q] [AddCommGroup T] where
  shift : T → Q → Q
  shift_zero : ∀ a, shift 0 a = a
  shift_add : ∀ t t' a, shift (t + t') a = shift t (shift t' a)
  shift_mul : ∀ t a b, shift t (a * b) = shift t a * shift t b
  shift_sSup : ∀ t (S : Set Q), shift t (sSup S) = ⨆ s ∈ S, shift t s
  shift_bot : ∀ t, shift t ⊥ = ⊥
  shift_top : ∀ t, shift t ⊤ = ⊤

namespace TemporalQuantale

variable [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q] [AddCommGroup T]
variable [TemporalQuantale Q T]

theorem shift_sup (t : T) (a b : Q) : shift t (a ⊔ b) = shift t a ⊔ shift t b := by
  simpa only [sSup_pair, iSup_insert, iSup_singleton] using shift_sSup t {a, b}

theorem shift_mono (t : T) : Monotone (shift (Q := Q) t) := by
  intro a b hab
  rw [← sup_eq_right, ← shift_sup, sup_eq_right.mpr hab]

theorem shift_neg (t : T) (a : Q) : shift (-t) (shift t a) = a := by
  rw [← shift_add, neg_add_cancel, shift_zero]

theorem shift_neg' (t : T) (a : Q) : shift t (shift (-t) a) = a := by
  rw [← shift_add, add_neg_cancel, shift_zero]

/-- The supplied shift, with its inverse and order reflection retained. -/
def shiftOrderIso (t : T) : Q ≃o Q where
  toFun := shift t
  invFun := shift (-t)
  left_inv := shift_neg t
  right_inv := shift_neg' t
  map_rel_iff' {a b} := by
    change shift t a ≤ shift t b ↔ a ≤ b
    exact ⟨fun h => by simpa only [shift_neg] using shift_mono (-t) h, fun h => shift_mono t h⟩

@[simp] theorem shiftOrderIso_apply (t : T) (a : Q) : shiftOrderIso t a = shift t a := rfl

@[simp] theorem shiftOrderIso_symm_apply (t : T) (a : Q) :
    (shiftOrderIso t).symm a = shift (-t) a := rfl

theorem shift_injective (t : T) : Function.Injective (shift (Q := Q) t) :=
  (shiftOrderIso t).injective

theorem shift_surjective (t : T) : Function.Surjective (shift (Q := Q) t) :=
  (shiftOrderIso t).surjective

theorem shift_bijective (t : T) : Function.Bijective (shift (Q := Q) t) :=
  (shiftOrderIso t).bijective

/-- Past readout: evaluate at the negatively shifted time. -/
def lag (a : Q) (t : T) : Q := shift (-t) a

/-- Future readout: evaluate at the positively shifted time. -/
def lead (a : Q) (t : T) : Q := shift t a

def seqAnd (a b : Q) (t : T) : Q := a * shift t b

def seqOr (a b : Q) (t : T) : Q := a ⊔ shift t b

/-- Algebraic predictive implication, with an explicit shifted conclusion. -/
noncomputable def predImpl (a b : Q) (t : T) : Q := leftResiduate a (shift t b)

theorem lag_lead_inv (a : Q) (t : T) : lag (lead a t) t = a := shift_neg t a

theorem lead_lag_inv (a : Q) (t : T) : lead (lag a t) t = a := shift_neg' t a

theorem shift_residuate (t : T) (a b : Q) :
    shift t (leftResiduate a b) = leftResiduate (shift t a) (shift t b) :=
  map_leftResiduate (shiftOrderIso t) (shift_mul t) a b

theorem temporal_transitivity (a b c : Q) (t₁ t₂ : T) :
    predImpl a b t₁ * shift t₁ (predImpl b c t₂) ≤ predImpl a c (t₁ + t₂) := by
  unfold predImpl
  rw [shift_residuate, ← shift_add]
  exact quantaleImplies_trans a (shift t₁ b) (shift (t₁ + t₂) c)

theorem temporal_modus_ponens (a b : Q) (t : T) :
    a * predImpl a b t ≤ shift t b := by
  simpa only [predImpl, mul_comm] using modusPonens_left a (shift t b)

theorem shift_seqAnd (t s : T) (a b : Q) :
    shift s (seqAnd a b t) = seqAnd (shift s a) (shift s b) t := by
  simp only [seqAnd, shift_mul]
  congr 1
  rw [← shift_add, ← shift_add, add_comm]

theorem shift_predImpl (t s : T) (a b : Q) :
    shift s (predImpl a b t) = predImpl (shift s a) (shift s b) t := by
  simp only [predImpl, shift_residuate]
  congr 1
  rw [← shift_add, ← shift_add, add_comm]

end TemporalQuantale

section IdentityExample
variable {Q : Type*} [CommSemigroup Q] [CompleteLattice Q] [IsCommQuantale Q]

/-- Static values, for which time carries no additional distinctions. -/
@[reducible] def TemporalQuantale.identity : TemporalQuantale Q ℤ where
  shift _ a := a
  shift_zero _ := rfl
  shift_add _ _ _ := rfl
  shift_mul _ _ _ := rfl
  shift_sSup _ _ := sSup_eq_iSup
  shift_bot _ := rfl
  shift_top _ := rfl
end IdentityExample

namespace TemporalQuantale
open Mettapedia.Algebra.FootprintQuantale

variable {Time Event : Type*} [AddCommGroup Time]

/-- Pull back timestamped labels along addition; reverse inclusion remains explicit. -/
def footprintShift (t : Time) :
    CompleteLatticeHom (Footprint (Time × Event)) (Footprint (Time × Event)) :=
  (CompleteLatticeHom.setPreimage (fun p : Time × Event => (p.1 + t, p.2))).dual

@[simp] theorem footprintShift_labels (t : Time) (q : Footprint (Time × Event)) :
    (footprintShift t q).labels = {p | (p.1 + t, p.2) ∈ q.labels} := rfl

/-- Timestamp transport over the existing footprint quantale, supplied explicitly. -/
@[instance_reducible] def timedFootprint : TemporalQuantale (Footprint (Time × Event)) Time where
  shift t q := footprintShift t q
  shift_zero q := by
    change ({p | (p.1 + 0, p.2) ∈ q.labels} : Set (Time × Event)) = q.labels
    simp only [add_zero, Prod.mk.eta, Set.ofPred_mem_eq]
  shift_add t t' q := by
    change ({p | (p.1 + (t + t'), p.2) ∈ q.labels} : Set (Time × Event)) =
      {p | ((p.1 + t) + t', p.2) ∈ q.labels}
    simp only [add_assoc]
  shift_mul _ _ _ := rfl
  shift_sSup t family := by
    have mapped := (footprintShift (Event := Event) t).map_sSup' family
    simpa only [CompleteLatticeHom.toFun_eq_coe, sSup_image] using mapped
  shift_bot _ := rfl
  shift_top _ := rfl

namespace Controls

/-- Distinct confidence values defeat antisymmetry of a strength-only order. -/
theorem strength_only_order_failure :
    let first : ℚ × ℚ := (0, 0)
    let second : ℚ × ℚ := (0, 1)
    first ≠ second ∧ first.1 ≤ second.1 ∧ second.1 ≤ first.1 := by decide

/-- An event at time zero is observed at time minus one after a unit shift. -/
theorem unit_shift_moves_event :
    footprintShift (Event := Unit) (1 : ℤ) (Footprint.ofSet {(0, ())}) ≠
      Footprint.ofSet {(0, ())} := by
  intro same
  have observed := congrArg (fun q : Footprint (ℤ × Unit) => (-1, ()) ∈ q.labels) same
  simp at observed

end Controls
end TemporalQuantale
