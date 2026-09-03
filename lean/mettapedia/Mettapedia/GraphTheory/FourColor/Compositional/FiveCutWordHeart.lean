import Mettapedia.GraphTheory.FourColor.CAP5YCapWords
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCycleColorClass

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

/-! ## Canonicalization at the root -/

open FiveCycleColorClass

theorem isTaitColorTriple_rotate {a b c : Color}
    (h : IsTaitColorTriple a b c) : IsTaitColorTriple c a b := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := h
  exact ⟨hc, ha, hb, fun h => hac h.symm, fun h => hbc h.symm, hab⟩

/-- The three canonical `Y₀`-cap words: the doubled colour is red, the third
red sits at position 4, 3, or 2, and the two minority letters read purple
then blue in boundary order. -/
def rootWord₁ : CAP5BoundaryWord := fun i =>
  if i = 2 then purple else if i = 3 then blue else red
def rootWord₂ : CAP5BoundaryWord := fun i =>
  if i = 2 then purple else if i = 4 then blue else red
def rootWord₃ : CAP5BoundaryWord := fun i =>
  if i = 3 then purple else if i = 4 then blue else red

/-- Any language word supported by the `Y₀` cap yields one of the three
canonical root words, using colour closure. -/
theorem root_canonicalization {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) {w : CAP5BoundaryWord}
    (hw : L w) (hcap : CAP5YCapSupport 0 w) :
    L rootWord₁ ∨ L rootWord₂ ∨ L rootWord₃ := by
  obtain ⟨hcapEq, hne, htriple⟩ := hcap
  have h2 : (0 : Fin 5) + 2 = 2 := by decide
  have h3 : (0 : Fin 5) + 3 = 3 := by decide
  have h4 : (0 : Fin 5) + 4 = 4 := by decide
  rw [h2, h3, h4] at htriple
  -- exactly one of the three vertex ports repeats the doubled colour
  have hmem : w 2 = w 0 ∨ w 3 = w 0 ∨ w 4 = w 0 := by
    have h2c := htriple.1
    have h3c := htriple.2.1
    have h4c := htriple.2.2.1
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (w 0) hne with h | h | h <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (w 2) h2c with g2 | g2 | g2 <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (w 3) h3c with g3 | g3 | g3 <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (w 4) h4c with g4 | g4 | g4 <;>
      first
        | exact Or.inl (g2.trans h.symm)
        | exact Or.inr (Or.inl (g3.trans h.symm))
        | exact Or.inr (Or.inr (g4.trans h.symm))
        | (exfalso
           obtain ⟨_, _, _, hab, hac, hbc⟩ := htriple
           first
             | exact hab (g2.trans g3.symm)
             | exact hac (g2.trans g4.symm)
             | exact hbc (g3.trans g4.symm))
  have h01 : (0 : Fin 5) + 1 = 1 := by decide
  rw [h01] at hcapEq
  have htargetPB : IsTaitColorTriple red purple blue :=
    isTaitColorTriple_swap_last isTaitColorTriple_red_blue_purple
  rcases hmem with hcase | hcase | hcase
  · -- third doubled letter at position 2: canonical shape ₃
    right; right
    have hsource : IsTaitColorTriple (w 0) (w 3) (w 4) := by
      rw [← hcase]; exact htriple
    have hmap := hL.colourClosed
      (equivalenceBetweenTaitTriples hsource htargetPB)
      (equivalenceBetweenTaitTriples_zero hsource htargetPB) w hw
    have heq : cap5MapBoundaryWord
        (equivalenceBetweenTaitTriples hsource htargetPB) w = rootWord₃ := by
      funext i
      fin_cases i <;>
        simp [cap5MapBoundaryWord, rootWord₃, ← hcapEq, hcase,
          equivalenceBetweenTaitTriples_first hsource htargetPB,
          equivalenceBetweenTaitTriples_second hsource htargetPB,
          equivalenceBetweenTaitTriples_third hsource htargetPB]
    rwa [heq] at hmap
  · -- third doubled letter at position 3: canonical shape ₂
    right; left
    have hsource : IsTaitColorTriple (w 0) (w 2) (w 4) := by
      have := isTaitColorTriple_swap_last
        (isTaitColorTriple_rotate (isTaitColorTriple_rotate htriple))
      rwa [hcase] at this
    have hmap := hL.colourClosed
      (equivalenceBetweenTaitTriples hsource htargetPB)
      (equivalenceBetweenTaitTriples_zero hsource htargetPB) w hw
    have heq : cap5MapBoundaryWord
        (equivalenceBetweenTaitTriples hsource htargetPB) w = rootWord₂ := by
      funext i
      fin_cases i <;>
        simp [cap5MapBoundaryWord, rootWord₂, ← hcapEq, hcase,
          equivalenceBetweenTaitTriples_first hsource htargetPB,
          equivalenceBetweenTaitTriples_second hsource htargetPB,
          equivalenceBetweenTaitTriples_third hsource htargetPB]
    rwa [heq] at hmap
  · -- third doubled letter at position 4: canonical shape ₁
    left
    have hsource : IsTaitColorTriple (w 0) (w 2) (w 3) := by
      have := isTaitColorTriple_rotate htriple
      rwa [hcase] at this
    have hmap := hL.colourClosed
      (equivalenceBetweenTaitTriples hsource htargetPB)
      (equivalenceBetweenTaitTriples_zero hsource htargetPB) w hw
    have heq : cap5MapBoundaryWord
        (equivalenceBetweenTaitTriples hsource htargetPB) w = rootWord₁ := by
      funext i
      fin_cases i <;>
        simp [cap5MapBoundaryWord, rootWord₁, ← hcapEq, hcase,
          equivalenceBetweenTaitTriples_first hsource htargetPB,
          equivalenceBetweenTaitTriples_second hsource htargetPB,
          equivalenceBetweenTaitTriples_third hsource htargetPB]
    rwa [heq] at hmap

/-! ## Orbit facts and the six computable colour equivalences -/

/-- Every zero-fixing colour relabelling of `w` lies in `L`. -/
def OrbitIn (L : CAP5BoundaryWord → Prop) (w : CAP5BoundaryWord) : Prop :=
  ∀ σ : Color ≃ Color, σ 0 = 0 → L (cap5MapBoundaryWord σ w)

/-- No zero-fixing colour relabelling of `w` lies in `L`. -/
def OrbitOut (L : CAP5BoundaryWord → Prop) (w : CAP5BoundaryWord) : Prop :=
  ∀ σ : Color ≃ Color, σ 0 = 0 → ¬ L (cap5MapBoundaryWord σ w)

theorem orbitIn_of_mem {L : CAP5BoundaryWord → Prop}
    (hL : BoundaryLanguage L) {w : CAP5BoundaryWord} (hw : L w) :
    OrbitIn L w :=
  fun σ hσ => hL.colourClosed σ hσ w hw

theorem orbitOut_of_disjoint {LA LB : CAP5BoundaryWord → Prop}
    (hdisj : ∀ w, ¬ (LA w ∧ LB w)) {w : CAP5BoundaryWord}
    (hin : OrbitIn LA w) : OrbitOut LB w :=
  fun σ hσ hmem => hdisj _ ⟨hin σ hσ, hmem⟩

/-- The colour table sending `red, blue, purple` to the given images. -/
def tableFun (r b p : Color) : Color → Color := fun c =>
  if c = red then r else if c = blue then b else if c = purple then p else 0

/-- The six zero-fixing colour equivalences, by their images of
`(red, blue, purple)`. -/
def σRBP : Color ≃ Color :=
  ⟨tableFun red blue purple, tableFun red blue purple, by decide, by decide⟩
def σRPB : Color ≃ Color :=
  ⟨tableFun red purple blue, tableFun red purple blue, by decide, by decide⟩
def σBRP : Color ≃ Color :=
  ⟨tableFun blue red purple, tableFun blue red purple, by decide, by decide⟩
def σPBR : Color ≃ Color :=
  ⟨tableFun purple blue red, tableFun purple blue red, by decide, by decide⟩
def σBPR : Color ≃ Color :=
  ⟨tableFun blue purple red, tableFun purple red blue, by decide, by decide⟩
def σPRB : Color ≃ Color :=
  ⟨tableFun purple red blue, tableFun blue purple red, by decide, by decide⟩

@[simp] theorem σRBP_zero : σRBP 0 = 0 := by decide
@[simp] theorem σRPB_zero : σRPB 0 = 0 := by decide
@[simp] theorem σBRP_zero : σBRP 0 = 0 := by decide
@[simp] theorem σPBR_zero : σPBR 0 = 0 := by decide
@[simp] theorem σBPR_zero : σBPR 0 = 0 := by decide
@[simp] theorem σPRB_zero : σPRB 0 = 0 := by decide

end FiveCutWordHeart

end Compositional

end Mettapedia.GraphTheory.FourColor
