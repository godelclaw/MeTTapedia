import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Germ.Basic

/-!
# Cofinite reduced powers: explicit tails and library germs

The constructive `Tail` presentation retains concrete thresholds and proves
relative infinity and incomparable oscillators without classical choice.
The order isomorphism below sends each tail class to the germ of the same
sequence. Library-germ results reuse those constructive proofs; the bridge
itself inherits the generic filter infrastructure's classical dependencies.
-/

set_option autoImplicit false
namespace Mettapedia.UniversalAlgebra.CofiniteReducedPower
open Filter

abbrev Carrier (Value : Type*) : Type _ := Filter.Germ (Filter.cofinite : Filter Nat) Value

def diagonal {Value : Type*} (value : Value) : Carrier Value := (value : Carrier Value)
def growing : Carrier Nat := (fun index : Nat => index : Carrier Nat)
def evenHigh : Carrier Nat :=
  (fun index : Nat => if index % 2 = 0 then 1 else 0 : Carrier Nat)
def oddHigh : Carrier Nat :=
  (fun index : Nat => if index % 2 = 0 then 0 else 1 : Carrier Nat)

namespace Tail

universe u

def EventuallyEqual {Value : Type u} (first second : Nat → Value) : Prop :=
  ∃ threshold : Nat, ∀ index : Nat, threshold ≤ index →
    first index = second index

/-- Combine two explicit tail bounds without choosing representatives or a filter. -/
private theorem combineTails {P Q R : Nat → Prop}
    (first : ∃ n, ∀ i, n ≤ i → P i) (second : ∃ n, ∀ i, n ≤ i → Q i)
    (combine : ∀ i, P i → Q i → R i) : ∃ n, ∀ i, n ≤ i → R i := by
  obtain ⟨n, hn⟩ := first
  obtain ⟨m, hm⟩ := second
  exact ⟨max n m, fun i hi => combine i (hn i ((le_max_left ..).trans hi))
    (hm i ((le_max_right ..).trans hi))⟩

theorem eventuallyEqual_refl {Value : Type u} (sequence : Nat → Value) :
    EventuallyEqual sequence sequence :=
  ⟨0, fun _index _bound => rfl⟩

theorem eventuallyEqual_symm {Value : Type u}
    {first second : Nat → Value}
    (equal : EventuallyEqual first second) :
    EventuallyEqual second first := by
  obtain ⟨threshold, equalAfter⟩ := equal
  exact ⟨threshold, fun index bound => (equalAfter index bound).symm⟩

theorem eventuallyEqual_trans {Value : Type u}
    {first second third : Nat → Value}
    (firstSecond : EventuallyEqual first second)
    (secondThird : EventuallyEqual second third) :
    EventuallyEqual first third :=
  combineTails firstSecond secondThird (fun _ => Eq.trans)

def sequenceSetoid (Value : Type u) : Setoid (Nat → Value) where
  r := EventuallyEqual
  iseqv :=
    ⟨fun sequence => eventuallyEqual_refl sequence,
      fun {_first _second} equal => eventuallyEqual_symm equal,
      fun {_first _second _third} firstSecond secondThird =>
        eventuallyEqual_trans firstSecond secondThird⟩

def Carrier (Value : Type u) : Type u :=
  Quotient (sequenceSetoid Value)

def ofSequence {Value : Type u} (sequence : Nat → Value) : Carrier Value :=
  Quotient.mk (sequenceSetoid Value) sequence

def diagonal {Value : Type u} (value : Value) : Carrier Value :=
  ofSequence fun _index => value

def growing : Carrier Nat :=
  ofSequence fun index => index

def EventuallyLE {Value : Type u} [LE Value]
    (first second : Nat → Value) : Prop :=
  ∃ threshold : Nat, ∀ index : Nat, threshold ≤ index →
    first index ≤ second index

theorem eventuallyLE_transport {Value : Type u} [LE Value]
    {first first' second second' : Nat → Value}
    (firstEqual : EventuallyEqual first first')
    (secondEqual : EventuallyEqual second second')
    (below : EventuallyLE first second) :
    EventuallyLE first' second' :=
  combineTails firstEqual (combineTails secondEqual below (fun _ => And.intro))
    (fun _ hf h => by rw [← hf, ← h.1]; exact h.2)

theorem eventuallyLE_congr {Value : Type u} [LE Value]
    {first first' second second' : Nat → Value}
    (firstEqual : EventuallyEqual first first')
    (secondEqual : EventuallyEqual second second') :
    EventuallyLE first second ↔ EventuallyLE first' second' :=
  ⟨eventuallyLE_transport firstEqual secondEqual,
    eventuallyLE_transport
      (eventuallyEqual_symm firstEqual)
      (eventuallyEqual_symm secondEqual)⟩

def le {Value : Type u} [LE Value]
    (first second : Carrier Value) : Prop :=
  Quotient.liftOn₂ first second EventuallyLE
    (fun _first _second _first' _second' firstEqual secondEqual =>
      propext (eventuallyLE_congr firstEqual secondEqual))

instance {Value : Type u} [LE Value] : LE (Carrier Value) :=
  ⟨le⟩

instance {Value : Type u} [Preorder Value] : Preorder (Carrier Value) where
  le_refl value := by
    refine Quotient.inductionOn' value ?_
    intro sequence
    exact ⟨0, fun index _bound => le_refl (sequence index)⟩
  le_trans first second third := by
    refine Quotient.inductionOn₃' first second third ?_
    exact fun _ _ _ firstBelow secondBelow =>
      combineTails firstBelow secondBelow (fun _ => le_trans)

instance {Value : Type u} [PartialOrder Value] : PartialOrder (Carrier Value) where
  le_antisymm first second := by
    refine Quotient.inductionOn₂' first second ?_
    exact fun _ _ firstBelow secondBelow =>
      Quotient.sound (combineTails firstBelow secondBelow (fun _ => le_antisymm))

theorem diagonal_injective :
    Function.Injective (diagonal : Nat → Carrier Nat) := by
  intro first second equalClasses
  obtain ⟨threshold, equalAt⟩ := Quotient.eq''.mp equalClasses
  exact equalAt threshold (le_refl threshold)

theorem diagonal_le_growing (value : Nat) :
    diagonal value ≤ growing :=
  ⟨value, fun _index bound => bound⟩

theorem growing_ne_diagonal (value : Nat) :
    growing ≠ diagonal value := by
  intro equalClasses
  obtain ⟨threshold, equalAt⟩ := Quotient.eq''.mp equalClasses
  have impossible := equalAt (max threshold (value + 1)) (le_max_left ..)
  dsimp at impossible
  omega

theorem diagonal_lt_growing (value : Nat) :
    diagonal value < growing := by
  rw [lt_iff_le_and_ne]
  exact ⟨diagonal_le_growing value, (growing_ne_diagonal value).symm⟩

theorem diagonal_not_surjective :
    ¬ Function.Surjective (diagonal : Nat → Carrier Nat) := by
  intro diagonalSurjective
  obtain ⟨value, valueMaps⟩ := diagonalSurjective growing
  exact growing_ne_diagonal value valueMaps.symm

def evenHigh : Carrier Nat :=
  ofSequence fun index => if index % 2 = 0 then 1 else 0

def oddHigh : Carrier Nat :=
  ofSequence fun index => if index % 2 = 0 then 0 else 1

theorem not_evenHigh_le_oddHigh : ¬ evenHigh ≤ oddHigh := by
  intro below
  obtain ⟨threshold, belowAfter⟩ := below
  have atEven := belowAfter (2 * threshold) (by omega)
  have evenRemainder : (2 * threshold) % 2 = 0 := by omega
  simp only [evenRemainder, ↓reduceIte] at atEven
  omega

theorem not_oddHigh_le_evenHigh : ¬ oddHigh ≤ evenHigh := by
  intro below
  obtain ⟨threshold, belowAfter⟩ := below
  have atOdd := belowAfter (2 * threshold + 1) (by omega)
  have oddRemainder : (2 * threshold + 1) % 2 ≠ 0 := by omega
  simp only [oddRemainder, ↓reduceIte] at atOdd
  omega

theorem oscillators_incomparable :
    (¬ evenHigh ≤ oddHigh) ∧ (¬ oddHigh ≤ evenHigh) :=
  ⟨not_evenHigh_le_oddHigh, not_oddHigh_le_evenHigh⟩

theorem relative_infinity :
    (∀ value : Nat, diagonal value < growing) ∧
      ¬ Function.Surjective (diagonal : Nat → Carrier Nat) :=
  ⟨diagonal_lt_growing, diagonal_not_surjective⟩

end Tail

/-- Representation change preserves the supplied sequences and their eventual order. -/
def tailGermOrderIso {Value : Type*} [PartialOrder Value] : Tail.Carrier Value ≃o Carrier Value where
  toEquiv := Quotient.congr (Equiv.refl _) (by
    intro first second
    change (∃ n, ∀ i, n ≤ i → first i = second i) ↔
      ∀ᶠ i in (Filter.cofinite : Filter Nat), first i = second i
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop])
  map_rel_iff' := by
    intro first second
    refine Quotient.inductionOn₂' first second ?_
    intro f g
    change (∀ᶠ i in (Filter.cofinite : Filter Nat), f i ≤ g i) ↔
      ∃ n, ∀ i, n ≤ i → f i ≤ g i
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]

@[simp] theorem tailGermOrderIso_ofSequence {Value : Type*} [PartialOrder Value]
    (sequence : Nat → Value) :
    tailGermOrderIso (Tail.ofSequence sequence) = (sequence : Carrier Value) := rfl

theorem diagonal_injective : Function.Injective (diagonal : Nat → Carrier Nat) :=
  fun _ _ equal => Tail.diagonal_injective (tailGermOrderIso.injective equal)

theorem diagonal_le_growing (value : Nat) : diagonal value ≤ growing :=
  tailGermOrderIso.monotone (Tail.diagonal_le_growing value)

theorem growing_ne_diagonal (value : Nat) : growing ≠ diagonal value :=
  fun equal => Tail.growing_ne_diagonal value (tailGermOrderIso.injective equal)

theorem diagonal_lt_growing (value : Nat) : diagonal value < growing :=
  tailGermOrderIso.strictMono (Tail.diagonal_lt_growing value)

theorem diagonal_not_surjective : ¬ Function.Surjective (diagonal : Nat → Carrier Nat) := by
  intro surjective
  obtain ⟨value, equal⟩ := surjective growing
  exact growing_ne_diagonal value equal.symm

theorem not_evenHigh_le_oddHigh : ¬ evenHigh ≤ oddHigh :=
  fun below => Tail.not_evenHigh_le_oddHigh (tailGermOrderIso.le_iff_le.mp below)

theorem not_oddHigh_le_evenHigh : ¬ oddHigh ≤ evenHigh :=
  fun below => Tail.not_oddHigh_le_evenHigh (tailGermOrderIso.le_iff_le.mp below)

theorem oscillators_incomparable : (¬ evenHigh ≤ oddHigh) ∧ (¬ oddHigh ≤ evenHigh) :=
  ⟨not_evenHigh_le_oddHigh, not_oddHigh_le_evenHigh⟩

theorem cofinite_relative_infinity :
    (∀ value : Nat, diagonal value < growing) ∧
      ¬ Function.Surjective (diagonal : Nat → Carrier Nat) :=
  ⟨diagonal_lt_growing, diagonal_not_surjective⟩

/-- A two-valued sequence whose class is not constant. -/
def alternating : Carrier Bool :=
  (fun n : Nat => if n % 2 = 0 then false else true : Nat → Bool)

theorem alternating_ne_diagonal (value : Bool) : alternating ≠ diagonal value := by
  intro equal
  have h : ∀ᶠ n in (Filter.cofinite : Filter Nat),
      (if n % 2 = 0 then false else true) = value := Filter.Germ.coe_eq.mp equal
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h
  obtain ⟨n, after⟩ := h
  have even := after (2 * n) (by omega)
  have odd := after (2 * n + 1) (by omega)
  have heven : (2 * n) % 2 = 0 := by omega
  have hodd : (2 * n + 1) % 2 ≠ 0 := by omega
  simp only [heven, hodd, ↓reduceIte] at even odd
  exact Bool.noConfusion (even.trans odd.symm)

/-- The first-order property "at most two elements" is lost despite equational transfer. -/
theorem boolean_three_distinct_classes :
    ∃ a b c : Carrier Bool, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
  ⟨diagonal false, diagonal true, alternating,
    fun equal => Bool.noConfusion (Filter.Germ.const_inj.mp equal),
    (alternating_ne_diagonal false).symm, (alternating_ne_diagonal true).symm⟩

end Mettapedia.UniversalAlgebra.CofiniteReducedPower
