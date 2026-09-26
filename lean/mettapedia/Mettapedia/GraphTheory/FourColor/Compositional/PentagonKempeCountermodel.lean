import Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport

/-!
# The exceptional language satisfies the abstract Kempe rules

The thirty admissible words rejected by a pentagon form a nonempty
`BoundaryLanguage`: they satisfy parity, colour relabelling, and closure
under every component-union switch for a suitable noncrossing mate at each
word and colour pair. The matchings here are explicit finite functions.

This refutes deduction of pentagon compatibility from that abstract interface
alone. It does not realize the language by a planar graph: compatibility
between the matchings of one common physical graph is additional information.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport

open FiveCutWordHeart CyclicBoundaryMatching PentagonContextTensor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private instance : DecidablePred (Odd : Nat → Prop) := fun n =>
  decidable_of_iff (n % 2 = 1) Nat.odd_iff.symm

private instance (w : CAP5BoundaryWord) : Decidable (CAP5BoundaryWordIsNonzero w) := by
  unfold CAP5BoundaryWordIsNonzero; infer_instance

private instance (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasOddColorCounts w) := by
  unfold CAP5BoundaryWordHasOddColorCounts; infer_instance

private instance (m : Fin 5 → Fin 5) : Decidable (Function.Involutive m) := by
  unfold Function.Involutive; infer_instance

private instance (a b c d : Fin 5) : Decidable (ChordsCross a b c d) := by
  unfold ChordsCross; infer_instance

private instance (m : Fin 5 → Fin 5) : Decidable (IsNoncrossingMatching m) := by
  unfold IsNoncrossingMatching; infer_instance

private def BadOrbit (w : CAP5BoundaryWord) : Prop :=
  ∃ i : Fin 10, i ∈ bad ∧ ∃ r : Fin 6,
    w = cap5MapBoundaryWord (relabel r) (representative i)

private instance (w : CAP5BoundaryWord) : Decidable (BadOrbit w) := by
  unfold BadOrbit; infer_instance

private theorem relabel_exhaustive : ∀ σ : Color ≃ Color,
    σ 0 = 0 → ∃ r : Fin 6, σ = relabel r := by decide +kernel

private theorem badOrbit_admissible : ∀ i ∈ bad, ∀ r,
    CAP5BoundaryWordIsNonzero (cap5MapBoundaryWord (relabel r) (representative i)) ∧
    CAP5BoundaryWordHasOddColorCounts
      (cap5MapBoundaryWord (relabel r) (representative i)) := by decide +kernel

private theorem badOrbit_relabel : ∀ r s i, i ∈ bad →
    BadOrbit (cap5MapBoundaryWord (relabel r)
      (cap5MapBoundaryWord (relabel s) (representative i))) := by decide +kernel

/-- Choose the matching whose switch stays in the bad profile. The pair of
singleton colours has just one component; its mate swaps their positions. -/
private def exceptionalMate (i : Fin 10) (r : Fin 6) (x y : Color) : Fin 5 → Fin 5 :=
  let a := (relabel r).symm x
  let b := (relabel r).symm y
  if a = red ∨ b = red then
    let p : Fin 2 := if a = blue ∨ b = blue then 0 else 1
    mateOption i p (decide (target i p false ∉ bad))
  else Equiv.swap (slots i).1 (slots i).2.1

/-- Check every component union of the displayed mate, not just one switch. -/
private theorem exceptionalMate_certificate : ∀ i ∈ bad, ∀ r x y,
    x ≠ 0 → y ≠ 0 → x ≠ y →
    let w := cap5MapBoundaryWord (relabel r) (representative i)
    let m := exceptionalMate i r x y
    Function.Involutive m ∧
      (∀ k, m k ≠ k ↔ (w k = x ∨ w k = y)) ∧
      IsNoncrossingMatching m ∧
      ∀ T : Finset (Fin 5), (∀ k ∈ T, m k ∈ T) →
        BadOrbit (cap5BoundarySwap x y T w) := by
  intro i
  fin_cases i <;> decide +kernel

private theorem badOrbit_boundaryLanguage : BoundaryLanguage BadOrbit := by
  constructor
  · rintro w ⟨i, hi, r, rfl⟩
    exact badOrbit_admissible i hi r
  · intro σ hzero w hw
    obtain ⟨r, rfl⟩ := relabel_exhaustive σ hzero
    obtain ⟨i, hi, s, rfl⟩ := hw
    exact badOrbit_relabel r s i hi
  · rintro w ⟨i, hi, r, rfl⟩ x y hx hy hxy
    exact ⟨exceptionalMate i r x y, exceptionalMate_certificate i hi r x y hx hy hxy⟩

private theorem badOrbit_nonempty : ∃ w, BadOrbit w :=
  ⟨_, 1, by decide, 0, rfl⟩

private theorem badOrbit_avoids (w : CAP5BoundaryWord) (hw : BadOrbit w) :
    ¬ CAP5WordExtendsAcrossCycle w := by
  obtain ⟨i, hi, r, rfl⟩ := hw
  intro hext
  have hz : relabel r 0 = 0 := by fin_cases r <;> decide
  have hrep := (cap5WordExtendsAcrossCycle_map_equiv_iff_of_map_zero hz).mp hext
  exact (bad_iff_not_good i).mp hi ((representative_extends_iff i).mp hrep)

/-- Parity and separate noncrossing Kempe closure do not exclude the exact
exceptional thirty-word language. -/
theorem rejected_boundaryLanguage : BoundaryLanguage Rejected := by
  have heq := language_eq_rejected_of_avoids
    badOrbit_boundaryLanguage badOrbit_nonempty badOrbit_avoids
  exact heq ▸ badOrbit_boundaryLanguage

theorem rejected_nonempty : ∃ w, Rejected w := by
  have heq := language_eq_rejected_of_avoids
    badOrbit_boundaryLanguage badOrbit_nonempty badOrbit_avoids
  exact heq ▸ badOrbit_nonempty

/-- An explicit countermodel to abstract boundary-language sufficiency. -/
theorem exists_nonempty_boundaryLanguage_avoiding_pentagon :
    ∃ L : CAP5BoundaryWord → Prop, BoundaryLanguage L ∧ (∃ w, L w) ∧
      ∀ w, L w → ¬ CAP5WordExtendsAcrossCycle w :=
  ⟨Rejected, rejected_boundaryLanguage, rejected_nonempty, fun _ hw => hw.2.2⟩

end Mettapedia.GraphTheory.FourColor.Compositional.PentagonKempeSupport
