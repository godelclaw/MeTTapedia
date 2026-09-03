import Mettapedia.GraphTheory.FourColor.CAP5YCapWords
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

/-!
# The word-level heart of the trivial-five-cut theorem

Boundary languages of the two shores of a nontrivial cyclic five-edge cut
are: admissible (nonzero letters, odd colour counts), closed under global
zero-fixing colour equivalences, and chain-closed — every member word and
colour pair carries a noncrossing involutive boundary mate whose
component-union switches stay in the language.  Minimality of a
counterexample makes each language meet the pentagon support and the three
consecutive Y-cap supports.  This file will prove that two such languages
cannot be disjoint.

This module states the hypothesis bundle and proves the finite mate
dichotomies: on a four-port active set the noncrossing involutive mates are
exactly the two nested pairings, and on a two-port active set the mate is
forced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace FiveCutWordHeart

open CyclicBoundaryMatching

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The boundary language of one shore: admissible words, closed under
global colour relabelling, and chain-closed under noncrossing physical
mates. -/
structure BoundaryLanguage (L : CAP5BoundaryWord → Prop) : Prop where
  admissible : ∀ w, L w →
    CAP5BoundaryWordIsNonzero w ∧ CAP5BoundaryWordHasOddColorCounts w
  colourClosed : ∀ σ : Color ≃ Color, σ 0 = 0 →
    ∀ w, L w → L (cap5MapBoundaryWord σ w)
  chainClosed : ∀ w, L w → ∀ x y : Color, x ≠ 0 → y ≠ 0 → x ≠ y →
    ∃ mate : Fin 5 → Fin 5,
      Function.Involutive mate ∧
      (∀ i, mate i ≠ i ↔ (w i = x ∨ w i = y)) ∧
      IsNoncrossingMatching mate ∧
      ∀ T : Finset (Fin 5), (∀ i ∈ T, mate i ∈ T) →
        L (cap5BoundarySwap x y T w)

private instance (n : Nat) (first second third fourth : Fin n) :
    Decidable (ChordsCross first second third fourth) := by
  unfold ChordsCross
  infer_instance

private instance (n : Nat) (mate : Fin n → Fin n) :
    Decidable (IsNoncrossingMatching mate) := by
  unfold IsNoncrossingMatching
  infer_instance

private instance (mate : Fin 5 → Fin 5) :
    Decidable (Function.Involutive mate) := by
  unfold Function.Involutive
  infer_instance

/-- An explicit pairing of four boundary ports. -/
def pairingMate (a b c d : Fin 5) : Fin 5 → Fin 5 := fun i =>
  if i = a then b else if i = b then a
  else if i = c then d else if i = d then c else i

/-- **Mate dichotomy on four active ports.**  For every four-element active
set, an involutive noncrossing mate moving exactly those ports is one of the
two nested pairings.  Stated for each of the five concrete active sets. -/
theorem mate_dichotomy_0123 (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3))
    (hnc : IsNoncrossingMatching mate) :
    mate = pairingMate 0 1 2 3 ∨ mate = pairingMate 0 3 1 2 := by
  have h : ∀ i : Fin 5, mate (mate i) = i := hinv
  revert h hactive hnc
  revert mate
  decide

theorem mate_dichotomy_0124 (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) 
    (hnc : IsNoncrossingMatching mate) :
    mate = pairingMate 0 1 2 4 ∨ mate = pairingMate 0 4 1 2 := by
  have h : ∀ i : Fin 5, mate (mate i) = i := hinv
  revert h hactive hnc
  revert mate
  decide

theorem mate_dichotomy_0134 (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4))
    (hnc : IsNoncrossingMatching mate) :
    mate = pairingMate 0 1 3 4 ∨ mate = pairingMate 0 4 1 3 := by
  have h : ∀ i : Fin 5, mate (mate i) = i := hinv
  revert h hactive hnc
  revert mate
  decide

theorem mate_dichotomy_0234 (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4))
    (hnc : IsNoncrossingMatching mate) :
    mate = pairingMate 0 2 3 4 ∨ mate = pairingMate 0 4 2 3 := by
  have h : ∀ i : Fin 5, mate (mate i) = i := hinv
  revert h hactive hnc
  revert mate
  decide

theorem mate_dichotomy_1234 (mate : Fin 5 → Fin 5)
    (hinv : Function.Involutive mate)
    (hactive : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4))
    (hnc : IsNoncrossingMatching mate) :
    mate = pairingMate 1 2 3 4 ∨ mate = pairingMate 1 4 2 3 := by
  have h : ∀ i : Fin 5, mate (mate i) = i := hinv
  revert h hactive hnc
  revert mate
  decide

/-- **Forced mate on two active ports.** -/
theorem mate_forced_two :
    ∀ a b : Fin 5, a ≠ b →
      ∀ mate : Fin 5 → Fin 5,
        Function.Involutive mate →
        (∀ i : Fin 5, mate i ≠ i ↔ (i = a ∨ i = b)) →
        ∀ i : Fin 5, mate i = if i = a then b else if i = b then a else i := by
  decide

end FiveCutWordHeart

end Compositional

end Mettapedia.GraphTheory.FourColor
