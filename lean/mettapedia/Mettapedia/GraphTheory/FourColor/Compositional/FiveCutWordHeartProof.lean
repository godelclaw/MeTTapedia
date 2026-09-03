import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeart

/-!
# The twelve-case refutation for the five-cut word heart

Two boundary languages of the shores of a nontrivial cyclic five-edge cut
each meet the pentagon support and three consecutive Y-cap supports.  This
file proves they cannot be disjoint: `exists_common_word`.  The case
analysis follows a machine-extracted refutation tree; every branch either
canonicalizes a support witness, forces a Kempe-chain conclusion through
the noncrossing mate dichotomy, or lands two facts in contradiction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace FiveCutWordHeart

open CyclicBoundaryMatching

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192
set_option synthInstance.maxHeartbeats 1000000

private instance : DecidableEq Color := inferInstance

private instance : Fintype Color := inferInstance

private def wordBPRRR : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then purple else if i = 2 then red else if i = 3 then red else red

private def wordPRBRR : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then red else if i = 2 then blue else if i = 3 then red else red

private def wordBRPRR : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then red else if i = 2 then purple else if i = 3 then red else red

private def wordRBPRR : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then blue else if i = 2 then purple else if i = 3 then red else red

private def wordRPRBR : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then purple else if i = 2 then red else if i = 3 then blue else red

private def wordRRBPR : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then red else if i = 2 then blue else if i = 3 then purple else red

private def wordBBBPR : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then blue else if i = 2 then blue else if i = 3 then purple else red

private def wordPPBPR : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then purple else if i = 2 then blue else if i = 3 then purple else red

private def wordPBPPR : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then blue else if i = 2 then purple else if i = 3 then purple else red

private def wordBPPPR : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then purple else if i = 2 then purple else if i = 3 then purple else red

private def wordPRRRB : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then red else if i = 2 then red else if i = 3 then red else blue

private def wordPBBRB : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then blue else if i = 2 then blue else if i = 3 then red else blue

private def wordBPBRB : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then purple else if i = 2 then blue else if i = 3 then red else blue

private def wordPBRBB : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then blue else if i = 2 then red else if i = 3 then blue else blue

private def wordPRBBB : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then red else if i = 2 then blue else if i = 3 then blue else blue

private def wordBRPBB : CAP5BoundaryWord :=
  fun i => if i = 0 then blue else if i = 1 then red else if i = 2 then purple else if i = 3 then blue else blue

private def wordRBPBB : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then blue else if i = 2 then purple else if i = 3 then blue else blue

private def wordRBRRP : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then blue else if i = 2 then red else if i = 3 then red else purple

private def wordPPBRP : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then purple else if i = 2 then blue else if i = 3 then red else purple

private def wordRRRBP : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then red else if i = 2 then red else if i = 3 then blue else purple

private def wordPPRBP : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then purple else if i = 2 then red else if i = 3 then blue else purple

private def wordPRPBP : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then red else if i = 2 then purple else if i = 3 then blue else purple

private def wordRPPBP : CAP5BoundaryWord :=
  fun i => if i = 0 then red else if i = 1 then purple else if i = 2 then purple else if i = 3 then blue else purple

private def wordPBRPP : CAP5BoundaryWord :=
  fun i => if i = 0 then purple else if i = 1 then blue else if i = 2 then red else if i = 3 then purple else purple

/-- **The word-level heart of the trivial-five-cut theorem.**  Two boundary
languages that each meet the pentagon support and three consecutive Y-cap
supports share a word. -/
theorem exists_common_word {LA LB : CAP5BoundaryWord → Prop}
    (hA : BoundaryLanguage LA) (hB : BoundaryLanguage LB)
    (hAP5 : ∃ w, LA w ∧ CAP5WordExtendsAcrossCycle w)
    (hAY0 : ∃ w, LA w ∧ CAP5YCapSupport 0 w)
    (hAY1 : ∃ w, LA w ∧ CAP5YCapSupport 1 w)
    (hAY2 : ∃ w, LA w ∧ CAP5YCapSupport 2 w)
    (hBP5 : ∃ w, LB w ∧ CAP5WordExtendsAcrossCycle w)
    (hBY0 : ∃ w, LB w ∧ CAP5YCapSupport 0 w)
    (hBY1 : ∃ w, LB w ∧ CAP5YCapSupport 1 w)
    (hBY2 : ∃ w, LB w ∧ CAP5YCapSupport 2 w) :
    ∃ w, LA w ∧ LB w := by
  by_contra hcontra
  have hdisjAB : ∀ w, ¬ (LA w ∧ LB w) := fun w h => hcontra ⟨w, h⟩
  have hdisjBA : ∀ w, ¬ (LB w ∧ LA w) := fun w h => hcontra ⟨w, h.2, h.1⟩
  obtain ⟨wAP5, hwAP5, hsAP5⟩ := hAP5
  obtain ⟨wAY0, hwAY0, hsAY0⟩ := hAY0
  obtain ⟨wAY1, hwAY1, hsAY1⟩ := hAY1
  obtain ⟨wAY2, hwAY2, hsAY2⟩ := hAY2
  obtain ⟨wBP5, hwBP5, hsBP5⟩ := hBP5
  obtain ⟨wBY0, hwBY0, hsBY0⟩ := hBY0
  obtain ⟨wBY1, hwBY1, hsBY1⟩ := hBY1
  obtain ⟨wBY2, hwBY2, hsBY2⟩ := hBY2
  rcases canonical_Y0 hA hwAY0 hsAY0 with hc1 | hc2 | hc3
  ·
    have h4 : ¬ LB wordRRPBR := by
      have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc1) σRBP (by decide)
      rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordRRPBR = wordRRPBR)] at hh
    rcases canonical_Y0 hB hwBY0 hsBY0 with hc5 | hc6 | hc7
    ·
      exact h4 hc5
    ·
      have h8 : ¬ LA wordBBPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc6) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBBPBR = wordBBPBR)] at hh
      have h9 : LA wordBRPBB := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordRRPBR hc1 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordRRPBR = wordBBPBR)] at hres
          exact h8 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRRPBR = wordBRPBB)] at hres
      have h10 : LA wordRBPRR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordRRPBR hc1 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordRRPBR = wordBBPBR)] at hres
          exact h8 hres
        ·
          have hcl : ∀ i ∈ ({1, 3} : Finset (Fin 5)), mate i ∈ ({1, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) wordRRPBR = wordRBPRR)] at hres
      have h11 : LB wordRBPBB := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordBBPBR hc6 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = red ∨ wordBBPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordBBPBR = wordRRPBR)] at hres
          exact h4 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordBBPBR = wordRBPBB)] at hres
      have h12 : LB wordBRPRR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordBBPBR hc6 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = red ∨ wordBBPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordBBPBR = wordRRPBR)] at hres
          exact h4 hres
        ·
          have hcl : ∀ i ∈ ({1, 3} : Finset (Fin 5)), mate i ∈ ({1, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) wordBBPBR = wordBRPRR)] at hres
      rcases canonical_Y1 hA hwAY1 hsAY1 with hc13 | hc14 | hc15
      ·
        have h16 : ¬ LA wordPBRBB := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h11) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordRBPBB = wordPBRBB)] at hh
        have h17 : LA wordPBBBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc13 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRRBR = wordPBBBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRRBR = wordPBRBB)] at hres
            exact h16 hres
        have h18 : LA wordPRRRB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc13 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPRRBR = wordPRRRB)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRRBR = wordPBRBB)] at hres
            exact h16 hres
        have h19 : LB wordPRBRR := by
          have hh := orbitIn_of_mem hB h11 σPRB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordRBPBB = wordPRBRR)] at hh
        have h20 : ¬ LB wordPBBRB := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc13) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRRBR = wordPBBRB)] at hh
        have h21 : LB wordPBRRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPRBRR h19 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRBRR i = red ∨ wordPRBRR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRBRR = wordPBRRR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRBRR = wordPBBRB)] at hres
            exact h20 hres
        have h22 : LB wordPRBBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPRBRR h19 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRBRR i = red ∨ wordPRBRR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPRBRR = wordPRBBB)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRBRR = wordPBBRB)] at hres
            exact h20 hres
        have h23 : LA wordRPBRR := by
          have hh := orbitIn_of_mem hA h9 σPRB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
        have h24 : ¬ LA wordBPRRR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h21) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBRRR = wordBPRRR)] at hh
        have h25 : LA wordBPBRB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordRPBRR h23 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
            exact h24 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRPBRR = wordBPBRB)] at hres
        have h26 : LA wordRPRBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordRPBRR h23 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
            exact h24 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordRPBRR = wordRPRBR)] at hres
        have h27 : ¬ LB wordRBPRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h9) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordBRPBB = wordRBPRR)] at hh
        have h28 : LB wordRBRRP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBRRR h21 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
            exact h27 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
        have h29 : LB wordPBPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBRRR h21 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
            exact h27 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({2, 3} : Finset (Fin 5)) wordPBRRR = wordPBPPR)] at hres
        have h30 : ¬ LA wordBPBBR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h28) σBPR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBPR) wordRBRRP = wordBPBBR)] at hh
        have h31 : LA wordBBBPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR h17 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
            exact h30 hres
          ·
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
        have h32 : LA wordPPPBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR h17 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
            exact h30 hres
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPPPBR)] at hres
        have h33 : ¬ LB wordPRRBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc13) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
        have h34 : ¬ LB wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h17) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
        have h35 : ¬ LB wordPPPBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h31) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBBBPR = wordPPPBR)] at hh
        rcases canonical_Y1 hB hwBY1 hsBY1 with hc36 | hc37 | hc38
        ·
          exact h33 hc36
        ·
          exact h34 hc37
        ·
          exact h35 hc38
      ·
        have h39 : ¬ LB wordRPBRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h9) σPRB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
        have h40 : ¬ LB wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc14) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
        rcases canonical_P5 hB hwBP5 hsBP5 with hc41 | hc42 | hc43 | hc44 | hc45
        ·
          have h46 : LA wordRPBRR := by
            have hh := orbitIn_of_mem hA h9 σPRB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
          have h47 : ¬ LA wordBPRRR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc41) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBRRR = wordBPRRR)] at hh
          have h48 : LA wordBPBRB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRPBRR h46 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
              exact h47 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRPBRR = wordBPBRB)] at hres
          have h49 : LA wordRPRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRPBRR h46 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
              exact h47 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordRPBRR = wordRPRBR)] at hres
          have h50 : ¬ LA wordPRBBB := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc41) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPBRRR = wordPRBBB)] at hh
          have h51 : LA wordPRRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h50 hres
          have h52 : LA wordPBBRB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPBBBR = wordPBBRB)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h50 hres
          have h53 : ¬ LB wordRBPRR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h9) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordBRPBB = wordRBPRR)] at hh
          have h54 : LB wordRBRRP := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBRRR hc41 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
              exact h53 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
          have h55 : LB wordPBPPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBRRR hc41 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
              exact h53 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({2, 3} : Finset (Fin 5)) wordPBRRR = wordPBPPR)] at hres
          have h56 : ¬ LA wordBPBBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h54) σBPR (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBPR) wordRBRRP = wordBPBBR)] at hh
          have h57 : LA wordBBBPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
              exact h56 hres
            ·
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
          have h58 : LA wordPPPBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
              exact h56 hres
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPPPBR)] at hres
          have h59 : ¬ LB wordPRRBR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h51) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
          have h60 : ¬ LB wordPPPBR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h57) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBBBPR = wordPPPBR)] at hh
          rcases canonical_Y1 hB hwBY1 hsBY1 with hc61 | hc62 | hc63
          ·
            exact h59 hc61
          ·
            exact h40 hc62
          ·
            exact h60 hc63
        ·
          exact h39 hc42
        ·
          exact h40 hc43
        ·
          exact h4 hc44
        ·
          have h64 : ¬ LA wordBBBPR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc45) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPPPBR = wordBBBPR)] at hh
          have h65 : LA wordBPBBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h64 hres
          have h66 : LA wordPBPPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBPPR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h64 hres
          have h67 : ¬ LA wordPPPBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc45) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
          have h68 : LA wordPRPBP := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRRPBR hc1 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
              exact h67 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordRRPBR = wordPRPBP)] at hres
          have h69 : LA wordRPRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRRPBR hc1 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
              exact h67 hres
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordRRPBR = wordRPRBR)] at hres
          have h70 : LB wordRPPBP := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPPPBR hc45 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
              exact h4 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
          have h71 : LB wordPRRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPPPBR hc45 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
              exact h4 hres
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPRRBR)] at hres
          have h72 : ¬ LA wordPRRBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h70) σPBR (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordRPPBP = wordPRRBR)] at hh
          have h73 : LA wordPRBBB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
              exact h72 hres
            ·
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
          have h74 : LA wordPBRRR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc14 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
              exact h72 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
          have h75 : ¬ LB wordPBRRR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h73) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
          have h76 : ¬ LB wordBPBBR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h65) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBPBBR = wordBPBBR)] at hh
          rcases canonical_Y2 hB hwBY2 hsBY2 with hc77 | hc78 | hc79
          ·
            exact h75 hc77
          ·
            exact h40 hc78
          ·
            exact h76 hc79
      ·
        have h80 : LA wordBPPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc15 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
            exact h8 hres
          ·
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
        have h81 : LA wordPBBBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc15 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
            exact h8 hres
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPBBBR)] at hres
        have h82 : ¬ LB wordPPPBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc15) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
        have h83 : LB wordPBPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordBBPBR hc6 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
            exact h82 hres
          ·
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordBBPBR = wordPBPPR)] at hres
        have h84 : LB wordBPBBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordBBPBR hc6 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
            exact h82 hres
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordBBPBR = wordBPBBR)] at hres
        have h85 : ¬ LB wordRPBRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h9) σPRB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
        have h86 : ¬ LB wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h80) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBPPPR = wordPBBBR)] at hh
        rcases canonical_P5 hB hwBP5 hsBP5 with hc87 | hc88 | hc89 | hc90 | hc91
        ·
          have h92 : LA wordRPBRR := by
            have hh := orbitIn_of_mem hA h9 σPRB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
          have h93 : ¬ LA wordBPRRR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc87) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBRRR = wordBPRRR)] at hh
          have h94 : LA wordBPBRB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRPBRR h92 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
              exact h93 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRPBRR = wordBPBRB)] at hres
          have h95 : LA wordRPRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordRPBRR h92 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
              exact h93 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordRPBRR = wordRPRBR)] at hres
          have h96 : ¬ LA wordPRBBB := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc87) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPBRRR = wordPRBBB)] at hh
          have h97 : LA wordPRRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR h81 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h96 hres
          have h98 : LA wordPBBRB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR h81 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPBBBR = wordPBBRB)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h96 hres
          have h99 : ¬ LB wordPRRBR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h97) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
          rcases canonical_Y1 hB hwBY1 hsBY1 with hc100 | hc101 | hc102
          ·
            exact h99 hc100
          ·
            exact h86 hc101
          ·
            exact h82 hc102
        ·
          exact h85 hc88
        ·
          exact h86 hc89
        ·
          exact h4 hc90
        ·
          exact h82 hc91
    ·
      have h103 : ¬ LA wordPPPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc7) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
      have h104 : LA wordPRPBP := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordRRPBR hc1 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
          exact h103 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordRRPBR = wordPRPBP)] at hres
      have h105 : LA wordRPRBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordRRPBR hc1 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
          exact h103 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordRRPBR = wordRPRBR)] at hres
      have h106 : LB wordRPPBP := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordPPPBR hc7 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
          exact h4 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
      have h107 : LB wordPRRBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordPPPBR hc7 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
          exact h4 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPRRBR)] at hres
      have h108 : ¬ LA wordPRRBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h106) σPBR (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordRPPBP = wordPRRBR)] at hh
      rcases canonical_Y1 hA hwAY1 hsAY1 with hc109 | hc110 | hc111
      ·
        exact h108 hc109
      ·
        have h112 : LA wordPRBBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR hc110 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h108 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
        have h113 : LA wordPBRRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR hc110 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h108 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
        have h114 : ¬ LA wordBBBPR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc7) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPPPBR = wordBBBPR)] at hh
        have h115 : LA wordBPBBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR hc110 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
            exact h114 hres
        have h116 : LA wordPBPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR hc110 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBPPR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
            exact h114 hres
        have h117 : ¬ LB wordPBRRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h112) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
        have h118 : ¬ LB wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc110) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
        have h119 : ¬ LB wordBPBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h115) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBPBBR = wordBPBBR)] at hh
        rcases canonical_Y2 hB hwBY2 hsBY2 with hc120 | hc121 | hc122
        ·
          exact h117 hc120
        ·
          exact h118 hc121
        ·
          exact h119 hc122
      ·
        exact h103 hc111
  ·
    have h123 : ¬ LB wordBBPBR := by
      have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc2) σRBP (by decide)
      rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBBPBR = wordBBPBR)] at hh
    rcases canonical_Y0 hB hwBY0 hsBY0 with hc124 | hc125 | hc126
    ·
      have h127 : ¬ LA wordRRPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc124) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordRRPBR = wordRRPBR)] at hh
      have h128 : LA wordRBPBB := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordBBPBR hc2 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = red ∨ wordBBPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordBBPBR = wordRRPBR)] at hres
          exact h127 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordBBPBR = wordRBPBB)] at hres
      have h129 : LA wordBRPRR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordBBPBR hc2 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = red ∨ wordBBPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordBBPBR = wordRRPBR)] at hres
          exact h127 hres
        ·
          have hcl : ∀ i ∈ ({1, 3} : Finset (Fin 5)), mate i ∈ ({1, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) wordBBPBR = wordBRPRR)] at hres
      have h130 : LB wordBRPBB := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordRRPBR hc124 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordRRPBR = wordBBPBR)] at hres
          exact h123 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRRPBR = wordBRPBB)] at hres
      have h131 : LB wordRBPRR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordRRPBR hc124 red blue (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = blue) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) wordRRPBR = wordBBPBR)] at hres
          exact h123 hres
        ·
          have hcl : ∀ i ∈ ({1, 3} : Finset (Fin 5)), mate i ∈ ({1, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) wordRRPBR = wordRBPRR)] at hres
      have h132 : ¬ LA wordRPBRR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h130) σPRB (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
      rcases canonical_P5 hA hwAP5 hsAP5 with hc133 | hc134 | hc135 | hc136 | hc137
      ·
        have h138 : ¬ LA wordRBPRR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h130) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordBRPBB = wordRBPRR)] at hh
        have h139 : LA wordRBRRP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBRRR hc133 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
            exact h138 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
        have h140 : LA wordPBPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBRRR hc133 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
            exact h138 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({2, 3} : Finset (Fin 5)) wordPBRRR = wordPBPPR)] at hres
        have h141 : LB wordRPBRR := by
          have hh := orbitIn_of_mem hB h130 σPRB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordBRPBB = wordRPBRR)] at hh
        have h142 : ¬ LB wordBPRRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc133) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBRRR = wordBPRRR)] at hh
        have h143 : LB wordBPBRB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRPBRR h141 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
            exact h142 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({0, 4} : Finset (Fin 5)) wordRPBRR = wordBPBRB)] at hres
        have h144 : LB wordRPRBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRPBRR h141 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = blue) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) wordRPBRR = wordBPRRR)] at hres
            exact h142 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordRPBRR = wordRPRBR)] at hres
        have h145 : ¬ LB wordPBRRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc133) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBRRR = wordPBRRR)] at hh
        have h146 : ¬ LB wordBPBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h139) σBPR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBPR) wordRBRRP = wordBPBBR)] at hh
        rcases canonical_Y2 hB hwBY2 hsBY2 with hc147 | hc148 | hc149
        ·
          exact h145 hc147
        ·
          have h150 : ¬ LB wordPRBBB := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc133) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPBRRR = wordPRBBB)] at hh
          have h151 : LB wordPRRBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc148 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h150 hres
          have h152 : LB wordPBBRB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc148 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPBBBR = wordPBBRB)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
              exact h150 hres
          have h153 : LB wordBBBPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc148 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
              exact h146 hres
            ·
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
          have h154 : LB wordPPPBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc148 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
              exact h146 hres
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPPPBR)] at hres
          have h155 : ¬ LA wordPRRBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h151) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
          have h156 : ¬ LA wordPBBBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc148) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
          have h157 : ¬ LA wordPPPBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h153) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBBBPR = wordPPPBR)] at hh
          rcases canonical_Y1 hA hwAY1 hsAY1 with hc158 | hc159 | hc160
          ·
            exact h155 hc158
          ·
            exact h156 hc159
          ·
            exact h157 hc160
        ·
          exact h146 hc149
      ·
        exact h132 hc134
      ·
        have h161 : ¬ LB wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc135) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
        rcases canonical_Y1 hB hwBY1 hsBY1 with hc162 | hc163 | hc164
        ·
          have h165 : LA wordPRBRR := by
            have hh := orbitIn_of_mem hA h128 σPRB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σPRB) wordRBPBB = wordPRBRR)] at hh
          have h166 : ¬ LA wordPBBRB := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc162) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRRBR = wordPBBRB)] at hh
          have h167 : LA wordPBRRR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPRBRR h165 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPRBRR i = red ∨ wordPRBRR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRBRR = wordPBRRR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRBRR = wordPBBRB)] at hres
              exact h166 hres
          have h168 : LA wordPRBBB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPRBRR h165 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPRBRR i = red ∨ wordPRBRR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({3, 4} : Finset (Fin 5)) wordPRBRR = wordPRBBB)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRBRR = wordPBBRB)] at hres
              exact h166 hres
          have h169 : ¬ LA wordRBPRR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h130) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordBRPBB = wordRBPRR)] at hh
          have h170 : LA wordRBRRP := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBRRR h167 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
              exact h169 hres
            ·
              have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
          have h171 : LA wordPBPPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBRRR h167 red purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
              exact h169 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red purple ({2, 3} : Finset (Fin 5)) wordPBRRR = wordPBPPR)] at hres
          have h172 : ¬ LB wordPBRRR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h167) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBRRR = wordPBRRR)] at hh
          have h173 : ¬ LB wordBPBBR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h170) σBPR (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBPR) wordRBRRP = wordBPBBR)] at hh
          rcases canonical_Y2 hB hwBY2 hsBY2 with hc174 | hc175 | hc176
          ·
            exact h172 hc174
          ·
            exact h161 hc175
          ·
            exact h173 hc176
        ·
          exact h161 hc163
        ·
          have h177 : ¬ LA wordBBBPR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc164) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPPPBR = wordBBBPR)] at hh
          have h178 : LA wordBPBBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc135 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h177 hres
          have h179 : LA wordPBPPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hA.chainClosed wordPBBBR hc135 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBPPR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h177 hres
          have h180 : ¬ LB wordBPPPR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc135) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBBBR = wordBPPPR)] at hh
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPPPBR hc164 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
            exact h123 hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
            exact h180 hres
      ·
        exact h127 hc136
      ·
        have h181 : LA wordRPPBP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc137 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
            exact h127 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
        have h182 : LA wordPRRBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc137 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
            exact h127 hres
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPRRBR)] at hres
        have h183 : ¬ LB wordPPPBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc137) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
        have h184 : LB wordPRPBP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRRPBR hc124 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
            exact h183 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordRRPBR = wordPRPBP)] at hres
        have h185 : LB wordRPRBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRRPBR hc124 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
            exact h183 hres
          ·
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordRRPBR = wordRPRBR)] at hres
        have h186 : ¬ LB wordPRRBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h181) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordRPPBP = wordPRRBR)] at hh
        rcases canonical_Y1 hB hwBY1 hsBY1 with hc187 | hc188 | hc189
        ·
          exact h186 hc187
        ·
          have h190 : LB wordPRBBB := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc188 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
              exact h186 hres
            ·
              have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
          have h191 : LB wordPBRRR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc188 red blue (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
            ·
              exfalso
              have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
              exact h186 hres
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
          have h192 : ¬ LB wordBBBPR := by
            have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc137) σRPB (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPPPBR = wordBBBPR)] at hh
          have h193 : LB wordBPBBR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc188 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h192 hres
          have h194 : LB wordPBPPR := by
            obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
              hB.chainClosed wordPBBBR hc188 blue purple (by decide) (by decide) (by decide)
            have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
            have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
            rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
            ·
              have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
              rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBPPR)] at hres
            ·
              exfalso
              have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
              have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
              rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
              exact h192 hres
          have h195 : ¬ LA wordPBRRR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h190) σBRP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
          have h196 : ¬ LA wordPBBBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc188) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
          have h197 : ¬ LA wordBPBBR := by
            have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h193) σRBP (by decide)
            rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBPBBR = wordBPBBR)] at hh
          rcases canonical_Y2 hA hwAY2 hsAY2 with hc198 | hc199 | hc200
          ·
            exact h195 hc198
          ·
            exact h196 hc199
          ·
            exact h197 hc200
        ·
          exact h183 hc189
    ·
      exact h123 hc125
    ·
      have h201 : ¬ LA wordPPPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc126) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
      have h202 : LA wordPBPPR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordBBPBR hc2 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
          exact h201 hres
        ·
          have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordBBPBR = wordPBPPR)] at hres
      have h203 : LA wordBPBBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordBBPBR hc2 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
          exact h201 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordBBPBR = wordBPBBR)] at hres
      have h204 : LB wordBPPPR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordPPPBR hc126 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
          exact h123 hres
        ·
          have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
      have h205 : LB wordPBBBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordPPPBR hc126 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
          exact h123 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPBBBR)] at hres
      have h206 : ¬ LA wordPBBBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h204) σRPB (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBPPPR = wordPBBBR)] at hh
      rcases canonical_Y1 hA hwAY1 hsAY1 with hc207 | hc208 | hc209
      ·
        have h210 : LA wordPBRBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc207 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRRBR = wordPBBBR)] at hres
            exact h206 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRRBR = wordPBRBB)] at hres
        have h211 : LA wordPRBRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc207 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRRBR = wordPBBBR)] at hres
            exact h206 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPRRBR = wordPRBRR)] at hres
        have h212 : ¬ LA wordRRRBP := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc126) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordPPPBR = wordRRRBP)] at hh
        have h213 : LA wordRPRBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc207 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPRRBR = wordRPRBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPRRBR = wordRRRBP)] at hres
            exact h212 hres
        have h214 : LA wordPRPBP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR hc207 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({2, 4} : Finset (Fin 5)), mate i ∈ ({2, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({2, 4} : Finset (Fin 5)) wordPRRBR = wordPRPBP)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPRRBR = wordRRRBP)] at hres
            exact h212 hres
        have h215 : ¬ LB wordPRRBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc207) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
        have h216 : LB wordPRBBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR h205 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h215 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
        have h217 : LB wordPBRRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR h205 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h215 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
        have h218 : ¬ LB wordRBRRP := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h202) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordPBPPR = wordRBRRP)] at hh
        have h219 : LB wordRBPRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBRRR h217 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
            exact h218 hres
        have h220 : LB wordPBRPP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBRRR h217 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({3, 4} : Finset (Fin 5)) wordPBRRR = wordPBRPP)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
            exact h218 hres
        have h221 : LB wordRPBRR := by
          have hh := orbitIn_of_mem hB h219 σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordRBPRR = wordRPBRR)] at hh
        have h222 : ¬ LB wordPRBRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h210) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPBRBB = wordPRBRR)] at hh
        have h223 : LB wordPPBRP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRPBRR h221 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRPBRR = wordPRBRR)] at hres
            exact h222 hres
          ·
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordRPBRR = wordPPBRP)] at hres
        have h224 : LB wordRRBPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordRPBRR h221 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordRPBRR i = red ∨ wordRPBRR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0134 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRPBRR = wordPRBRR)] at hres
            exact h222 hres
          ·
            have hcl : ∀ i ∈ ({1, 3} : Finset (Fin 5)), mate i ∈ ({1, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({1, 3} : Finset (Fin 5)) wordRPBRR = wordRRBPR)] at hres
        have h225 : ¬ LA wordPBRRR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h216) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
        have h226 : ¬ LA wordRPBRR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h219) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordRBPRR = wordRPBRR)] at hh
        have h227 : ¬ LA wordRRPBR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h223) σBPR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBPR) wordPPBRP = wordRRPBR)] at hh
        rcases canonical_P5 hA hwAP5 hsAP5 with hc228 | hc229 | hc230 | hc231 | hc232
        ·
          exact h225 hc228
        ·
          exact h226 hc229
        ·
          exact h206 hc230
        ·
          exact h227 hc231
        ·
          exact h201 hc232
      ·
        exact h206 hc208
      ·
        exact h201 hc209
  ·
    have h233 : ¬ LB wordPPPBR := by
      have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc3) σRBP (by decide)
      rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPPPBR = wordPPPBR)] at hh
    rcases canonical_Y0 hB hwBY0 hsBY0 with hc234 | hc235 | hc236
    ·
      have h237 : ¬ LA wordRRPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc234) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordRRPBR = wordRRPBR)] at hh
      have h238 : LA wordRPPBP := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordPPPBR hc3 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
          exact h237 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
      have h239 : LA wordPRRBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordPPPBR hc3 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
          exact h237 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPRRBR)] at hres
      have h240 : LB wordPRPBP := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordRRPBR hc234 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
          exact h233 hres
        ·
          have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordRRPBR = wordPRPBP)] at hres
      have h241 : LB wordRPRBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordRRPBR hc234 red purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordRRPBR i = red ∨ wordRRPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordRRPBR = wordPPPBR)] at hres
          exact h233 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap red purple ({1, 2} : Finset (Fin 5)) wordRRPBR = wordRPRBR)] at hres
      have h242 : ¬ LB wordPRRBR := by
        have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h238) σPBR (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordRPPBP = wordPRRBR)] at hh
      rcases canonical_Y1 hB hwBY1 hsBY1 with hc243 | hc244 | hc245
      ·
        exact h242 hc243
      ·
        have h246 : ¬ LA wordPBBBR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc244) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPBBBR = wordPBBBR)] at hh
        have h247 : LA wordPBRBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR h239 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRRBR = wordPBBBR)] at hres
            exact h246 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPRRBR = wordPBRBB)] at hres
        have h248 : LA wordPRBRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPRRBR h239 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPRRBR i = red ∨ wordPRRBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPRRBR = wordPBBBR)] at hres
            exact h246 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPRRBR = wordPRBRR)] at hres
        have h249 : ¬ LA wordBPPPR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc244) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPBBBR = wordBPPPR)] at hh
        have h250 : LA wordBBPBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc3 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
            exact h249 hres
        have h251 : LA wordPPBPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc3 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPPPBR = wordPPBPR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
            exact h249 hres
        have h252 : LB wordPRBBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR hc244 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h242 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
        have h253 : LB wordPBRRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR hc244 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h242 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
        have h254 : ¬ LB wordBBBPR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA hc3) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordPPPBR = wordBBBPR)] at hh
        have h255 : LB wordBPBBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR hc244 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPBBBR = wordBPBBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
            exact h254 hres
        have h256 : LB wordPBPPR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hB.chainClosed wordPBBBR hc244 blue purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = blue ∨ wordPBBBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap blue purple ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBPPR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPBBBR = wordBBBPR)] at hres
            exact h254 hres
        have h257 : ¬ LA wordPBRRR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h252) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
        have h258 : ¬ LA wordBPBBR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h255) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBPBBR = wordBPBBR)] at hh
        rcases canonical_Y2 hA hwAY2 hsAY2 with hc259 | hc260 | hc261
        ·
          exact h257 hc259
        ·
          exact h246 hc260
        ·
          exact h258 hc261
      ·
        exact h233 hc245
    ·
      have h262 : ¬ LA wordBBPBR := by
        have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc235) σRBP (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordBBPBR = wordBBPBR)] at hh
      have h263 : LA wordBPPPR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordPPPBR hc3 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
          exact h262 hres
        ·
          have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordPPPBR = wordBPPPR)] at hres
      have h264 : LA wordPBBBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hA.chainClosed wordPPPBR hc3 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordPPPBR i = blue ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordBBPBR)] at hres
          exact h262 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordPPPBR = wordPBBBR)] at hres
      have h265 : LB wordPBPPR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordBBPBR hc235 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
          exact h233 hres
        ·
          have hcl : ∀ i ∈ ({0, 3} : Finset (Fin 5)), mate i ∈ ({0, 3} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 3} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({0, 3} : Finset (Fin 5)) wordBBPBR = wordPBPPR)] at hres
      have h266 : LB wordBPBBR := by
        obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
          hB.chainClosed wordBBPBR hc235 blue purple (by decide) (by decide) (by decide)
        have hiff : ∀ i : Fin 5, ((wordBBPBR i = blue ∨ wordBBPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)) := by decide
        have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := fun i => (hact i).trans (hiff i)
        rcases mate_dichotomy_0123 mate hinv hact' hnc with hm | hm
        ·
          exfalso
          have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
          rw [(by decide : cap5BoundarySwap blue purple ({0, 1} : Finset (Fin 5)) wordBBPBR = wordPPPBR)] at hres
          exact h233 hres
        ·
          have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
          have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
          rwa [(by decide : cap5BoundarySwap blue purple ({1, 2} : Finset (Fin 5)) wordBBPBR = wordBPBBR)] at hres
      have h267 : ¬ LB wordPBBBR := by
        have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h263) σRPB (by decide)
        rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordBPPPR = wordPBBBR)] at hh
      rcases canonical_Y1 hB hwBY1 hsBY1 with hc268 | hc269 | hc270
      ·
        have h271 : ¬ LA wordPRRBR := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc268) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordPRRBR = wordPRRBR)] at hh
        have h272 : LA wordPRBBB := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR h264 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h271 hres
          ·
            have hcl : ∀ i ∈ ({1, 4} : Finset (Fin 5)), mate i ∈ ({1, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({1, 4} : Finset (Fin 5)) wordPBBBR = wordPRBBB)] at hres
        have h273 : LA wordPBRRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBBBR h264 red blue (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBBBR i = red ∨ wordPBBBR i = blue) ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_1234 mate hinv hact' hnc with hm | hm
          ·
            exfalso
            have hcl : ∀ i ∈ ({1, 2} : Finset (Fin 5)), mate i ∈ ({1, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({1, 2} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red blue ({1, 2} : Finset (Fin 5)) wordPBBBR = wordPRRBR)] at hres
            exact h271 hres
          ·
            have hcl : ∀ i ∈ ({2, 3} : Finset (Fin 5)), mate i ∈ ({2, 3} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 3} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) wordPBBBR = wordPBRRR)] at hres
        have h274 : ¬ LA wordRBRRP := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB h265) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordPBPPR = wordRBRRP)] at hh
        have h275 : LA wordRBPRR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBRRR h273 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 2} : Finset (Fin 5)), mate i ∈ ({0, 2} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 2} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 2} : Finset (Fin 5)) wordPBRRR = wordRBPRR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
            exact h274 hres
        have h276 : LA wordPBRPP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPBRRR h273 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPBRRR i = red ∨ wordPBRRR i = purple) ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0234 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({3, 4} : Finset (Fin 5)), mate i ∈ ({3, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({3, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({3, 4} : Finset (Fin 5)) wordPBRRR = wordPBRPP)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPBRRR = wordRBRRP)] at hres
            exact h274 hres
        have h277 : ¬ LA wordRPPBP := by
          have hh := orbitOut_of_disjoint hdisjBA (orbitIn_of_mem hB hc268) σPBR (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σPBR) wordPRRBR = wordRPPBP)] at hh
        have h278 : LA wordRRPBR := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc3 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({0, 1} : Finset (Fin 5)), mate i ∈ ({0, 1} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 1} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) wordPPPBR = wordRRPBR)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
            exact h277 hres
        have h279 : LA wordPPRBP := by
          obtain ⟨mate, hinv, hact, hnc, hswap⟩ :=
            hA.chainClosed wordPPPBR hc3 red purple (by decide) (by decide) (by decide)
          have hiff : ∀ i : Fin 5, ((wordPPPBR i = red ∨ wordPPPBR i = purple) ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4)) := by decide
          have hact' : ∀ i : Fin 5, mate i ≠ i ↔ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := fun i => (hact i).trans (hiff i)
          rcases mate_dichotomy_0124 mate hinv hact' hnc with hm | hm
          ·
            have hcl : ∀ i ∈ ({2, 4} : Finset (Fin 5)), mate i ∈ ({2, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({2, 4} : Finset (Fin 5)) hcl
            rwa [(by decide : cap5BoundarySwap red purple ({2, 4} : Finset (Fin 5)) wordPPPBR = wordPPRBP)] at hres
          ·
            exfalso
            have hcl : ∀ i ∈ ({0, 4} : Finset (Fin 5)), mate i ∈ ({0, 4} : Finset (Fin 5)) := by rw [hm]; decide
            have hres := hswap ({0, 4} : Finset (Fin 5)) hcl
            rw [(by decide : cap5BoundarySwap red purple ({0, 4} : Finset (Fin 5)) wordPPPBR = wordRPPBP)] at hres
            exact h277 hres
        have h280 : ¬ LB wordPBRRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h272) σBRP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σBRP) wordPRBBB = wordPBRRR)] at hh
        have h281 : ¬ LB wordRPBRR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h275) σRPB (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRPB) wordRBPRR = wordRPBRR)] at hh
        have h282 : ¬ LB wordRRPBR := by
          have hh := orbitOut_of_disjoint hdisjAB (orbitIn_of_mem hA h278) σRBP (by decide)
          rwa [(by decide : cap5MapBoundaryWord (⇑σRBP) wordRRPBR = wordRRPBR)] at hh
        rcases canonical_P5 hB hwBP5 hsBP5 with hc283 | hc284 | hc285 | hc286 | hc287
        ·
          exact h280 hc283
        ·
          exact h281 hc284
        ·
          exact h267 hc285
        ·
          exact h282 hc286
        ·
          exact h233 hc287
      ·
        exact h267 hc269
      ·
        exact h233 hc270
    ·
      exact h233 hc236

end FiveCutWordHeart

end Compositional

end Mettapedia.GraphTheory.FourColor
