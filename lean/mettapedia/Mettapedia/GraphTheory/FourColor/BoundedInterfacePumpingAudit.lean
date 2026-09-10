import Mettapedia.GraphTheory.FourColor.GoertzelV24CountSupportSynchronization
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamExchange

/-!
# Adversarial controls for bounded-interface pumping

Finite interface types do not imply finite exact Count values. Repeated support
cardinality does not license deletion, and support does not encode seam order.
These are controls against weakening the existing support-deletion theorem,
not refutations of that theorem or of geometric cut supply.

Universal terminal tests separate all abstract supports. Consequently any
encoding preserving every such test must distinguish all supports. This is
not a lower bound for the subset of supports realizable by planar tangles.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedInterfacePumpingAudit

open GoertzelV24CountSupportSynchronization

/-- One state and one generator already allow infinitely many exact rows. -/
def doublingRow (n : ℕ) : Unit → ℕ := fun _ => 2 ^ n

theorem doublingRow_step (n : ℕ) :
    rowMul (doublingRow n) (fun _ _ => 2) = doublingRow (n + 1) := by
  funext q
  simp [rowMul, doublingRow, pow_succ]

theorem doublingRow_injective : Function.Injective doublingRow := by
  intro n m h
  have hpow : 2 ^ n = 2 ^ m := congrFun h ()
  exact Nat.pow_right_injective (by decide) hpow

theorem doublingRow_support (n : ℕ) : rowSupport (doublingRow n) = Finset.univ := by
  ext q
  simp [doublingRow, pow_pos]

/-- No finite code can retain these exact counts losslessly. -/
theorem no_finite_exact_count_code (P : Type*) [Fintype P] :
    ¬ ∃ code : ℕ → P, ∀ n m, code n = code m → doublingRow n = doublingRow m := by
  rintro ⟨code, hcode⟩
  have hinj : Function.Injective code := fun n m h => doublingRow_injective (hcode n m h)
  exact (Infinite.not_finite : ¬ Finite ℕ) (Finite.of_injective code hinj)

def swapLetter (source target : Bool) : ℕ := if target = !source then 1 else 0

/-- Same interface, same support cardinality, opposite answer to a terminal test. -/
theorem cardinality_repeat_does_not_license_deletion :
    (runSupport [swapLetter] {false}).card = (runSupport [] {false}).card ∧
    ¬ ((runSupport [swapLetter] {false}) ∩ {false}).Nonempty ∧
    ((runSupport [] {false}) ∩ {false}).Nonempty := by decide

section TerminalTests

variable {Q : Type*} [DecidableEq Q]

def accepts (support terminal : Finset Q) : Prop := (support ∩ terminal).Nonempty

/-- Support equality is precisely indistinguishability by arbitrary terminal sets. -/
theorem support_eq_iff_terminal_tests (S T : Finset Q) :
    S = T ↔ ∀ terminal, accepts S terminal ↔ accepts T terminal := by
  constructor
  · rintro rfl
    exact fun _ => Iff.rfl
  · intro h
    ext q
    simpa [accepts, Finset.Nonempty] using h {q}

/-- A context-complete encoding on all abstract supports is injective. -/
theorem complete_code_injective {P : Type*} (code : Finset Q → P)
    (hcode : ∀ S T, code S = code T → ∀ terminal,
      accepts S terminal ↔ accepts T terminal) : Function.Injective code := by
  intro S T h
  exact (support_eq_iff_terminal_tests S T).mpr (hcode S T h)

theorem complete_code_card_lower_bound [Fintype Q] {P : Type*} [Fintype P]
    (code : Finset Q → P)
    (hcode : ∀ S T, code S = code T → ∀ terminal,
      accepts S terminal ↔ accepts T terminal) :
    2 ^ Fintype.card Q ≤ Fintype.card P := by
  simpa using Fintype.card_le_of_injective code (complete_code_injective code hcode)

end TerminalTests

/-- A three-port cyclic seam. -/
def cycle3 : Equiv.Perm (Fin 3) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by decide
  right_inv := by decide

/-- Adjacent positions on a cyclic port order must carry distinct colours. -/
def cycleAccepts {Q C : Type*} (rotation : Equiv.Perm Q) (word : Q → C) : Prop :=
  ∀ i, word i ≠ word (rotation i)

theorem cycleAccepts_inverse {Q C : Type*} (rotation : Equiv.Perm Q) (word : Q → C) :
    cycleAccepts rotation word ↔ cycleAccepts rotation.symm word := by
  constructor
  · intro h i
    simpa using (h (rotation.symm i)).symm
  · intro h i
    simpa using (h (rotation i)).symm

/-- For three ports this is the same nonempty proper-triple support in either order.
This is a seam-algebra control, not a constructed spherical graph counterexample. -/
theorem three_port_support_ignores_orientation :
    (∀ word : Fin 3 → Fin 3, cycleAccepts cycle3 word ↔ cycleAccepts cycle3.symm word) ∧
    cycleAccepts cycle3 (id : Fin 3 → Fin 3) := by
  exact ⟨fun word => cycleAccepts_inverse cycle3 word, by unfold cycleAccepts; decide⟩

/-- Even with identity port matching, repeated width does not fix seam orientation. -/
theorem seam_order_matters :
    GoertzelV24SeamExchange.OrientationReversing (Equiv.refl (Fin 3)) cycle3 cycle3.symm ∧
    ¬ GoertzelV24SeamExchange.OrientationReversing (Equiv.refl (Fin 3)) cycle3 cycle3 := by
  constructor
  · intro i
    rfl
  · intro h
    have hzero := h 0
    norm_num [cycle3] at hzero
    exact (by decide : (1 : Fin 3) ≠ -1) hzero

end Mettapedia.GraphTheory.FourColor.BoundedInterfacePumpingAudit
