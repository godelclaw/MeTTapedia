import Mettapedia.GraphTheory.FourColor.InternalEdgeOpening
import Mathlib.Logic.Relation

/-!
# A cofacial cycle-lifting obstruction

An explicit closed cubic graph has proper edge colourings, but its edges
8 and 9 lie on no common bichromatic component in any colouring. The
spherical embedding and inverse edge insertion are checked separately by
the companion constructor gate. This does not refute arbitrary recolouring
lifts or the minimal-counterexample route.
-/

namespace Mettapedia.GraphTheory.FourColor.SmoothingCycleObstruction

open InternalEdgeOpening

abbrev Edge := Fin 27
abbrev Coloring := Edge → Fin 3

def ends : Edge → Fin 18 × Fin 18 := ![
  (0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8),(3,9),(4,10),(4,11),(5,6),(5,12),(6,13),(7,8),(7,14),(8,9),(9,15),(10,11),(10,16),(11,12),(12,17),(13,14),(13,17),(14,15),(15,16),(16,17)]

def samples : Fin 6 → Coloring := ![
  ![0,1,2,1,2,0,2,0,1,2,0,1,0,2,1,0,2,0,1,0,2,1,1,0,2,1,2],
  ![0,1,2,1,2,2,0,0,1,2,0,0,1,1,1,2,2,0,1,0,2,0,0,2,1,2,1],
  ![0,1,2,2,1,0,2,0,1,1,0,2,0,1,1,0,2,0,2,0,1,2,2,0,1,2,1],
  ![0,1,2,2,1,0,2,1,0,1,0,2,0,1,0,1,2,1,2,0,1,2,2,0,0,2,1],
  ![0,1,2,2,1,2,0,0,1,0,1,0,2,1,1,2,2,0,2,1,0,1,0,2,1,2,0],
  ![0,1,2,2,1,2,0,0,1,1,0,0,2,1,1,2,2,0,2,0,1,0,0,2,1,2,1]]

theorem samples_proper : ∀ i, Proper ends (samples i) := by decide +kernel

private theorem force0 : ∀ x : Fin 3, x ≠ 1 → x ≠ 2 → x = 0 := by decide
private theorem force1 : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
private theorem force2 : ∀ x : Fin 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide
private theorem three : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
private theorem impossible : ∀ x : Fin 3, x ≠ 0 → x ≠ 1 → x ≠ 2 → False := by decide

theorem normalized_cases (c : Coloring) (hp : Proper ends c)
    (e0 : c 0 = 0) (e1 : c 1 = 1) (e2 : c 2 = 2) :
    ∃ i, c = samples i := by
  rcases three (c 3) with e3 | e3 | e3
  · exact False.elim (hp 3 0 (by decide) (by decide) (e3.trans e0.symm))
  · have e4 : c 4 = 2 := force2 _
      (by simpa only [e0] using hp 4 0 (by decide) (by decide))
      (by simpa only [e3] using hp 4 3 (by decide) (by decide))
    rcases three (c 5) with e5 | e5 | e5
    · have e6 : c 6 = 2 := force2 _
        (by simpa only [e5] using hp 6 5 (by decide) (by decide))
        (by simpa only [e1] using hp 6 1 (by decide) (by decide))
      have e11 : c 11 = 1 := force1 _
        (by simpa only [e5] using hp 11 5 (by decide) (by decide))
        (by simpa only [e4] using hp 11 4 (by decide) (by decide))
      have e12 : c 12 = 0 := force0 _
        (by simpa only [e11] using hp 12 11 (by decide) (by decide))
        (by simpa only [e4] using hp 12 4 (by decide) (by decide))
      have e13 : c 13 = 2 := force2 _
        (by simpa only [e5] using hp 13 5 (by decide) (by decide))
        (by simpa only [e11] using hp 13 11 (by decide) (by decide))
      rcases three (c 7) with e7 | e7 | e7
      · have e8 : c 8 = 1 := force1 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 1 := force1 _
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
        have e15 : c 15 = 0 := force0 _
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
        have e17 : c 17 = 0 := force0 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        have e22 : c 22 = 1 := force1 _
          (by simpa only [e15] using hp 22 15 (by decide) (by decide))
          (by simpa only [e13] using hp 22 13 (by decide) (by decide))
        have e23 : c 23 = 0 := force0 _
          (by simpa only [e22] using hp 23 22 (by decide) (by decide))
          (by simpa only [e13] using hp 23 13 (by decide) (by decide))
        have e24 : c 24 = 2 := force2 _
          (by simpa only [e15] using hp 24 15 (by decide) (by decide))
          (by simpa only [e22] using hp 24 22 (by decide) (by decide))
        have e25 : c 25 = 1 := force1 _
          (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          (by simpa only [e24] using hp 25 24 (by decide) (by decide))
        have e26 : c 26 = 2 := force2 _
          (by simpa only [e23] using hp 26 23 (by decide) (by decide))
          (by simpa only [e25] using hp 26 25 (by decide) (by decide))
        have e19 : c 19 = 0 := force0 _
          (by simpa only [e25] using hp 19 25 (by decide) (by decide))
          (by simpa only [e26] using hp 19 26 (by decide) (by decide))
        have e9 : c 9 = 2 := force2 _
          (by simpa only [e19] using hp 9 19 (by decide) (by decide))
          (by simpa only [e3] using hp 9 3 (by decide) (by decide))
        have e10 : c 10 = 0 := force0 _
          (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          (by simpa only [e9] using hp 10 9 (by decide) (by decide))
        have e18 : c 18 = 1 := force1 _
          (by simpa only [e10] using hp 18 10 (by decide) (by decide))
          (by simpa only [e9] using hp 18 9 (by decide) (by decide))
        have e20 : c 20 = 2 := force2 _
          (by simpa only [e10] using hp 20 10 (by decide) (by decide))
          (by simpa only [e18] using hp 20 18 (by decide) (by decide))
        have e21 : c 21 = 1 := force1 _
          (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          (by simpa only [e20] using hp 21 20 (by decide) (by decide))
        refine ⟨0, ?_⟩
        funext e
        fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e11, e12, e13, e7, e8, e14, e15, e16, e17, e22, e23, e24, e25, e26, e19, e9, e10, e18, e20, e21]
      · have e8 : c 8 = 0 := force0 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 0 := force0 _
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
        have e15 : c 15 = 1 := force1 _
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
        have e17 : c 17 = 1 := force1 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        have e22 : c 22 = 0 := force0 _
          (by simpa only [e15] using hp 22 15 (by decide) (by decide))
          (by simpa only [e13] using hp 22 13 (by decide) (by decide))
        have e23 : c 23 = 1 := force1 _
          (by simpa only [e22] using hp 23 22 (by decide) (by decide))
          (by simpa only [e13] using hp 23 13 (by decide) (by decide))
        have e21 : c 21 = 2 := force2 _
          (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          (by simpa only [e23] using hp 21 23 (by decide) (by decide))
        have e20 : c 20 = 1 := force1 _
          (by simpa only [e12] using hp 20 12 (by decide) (by decide))
          (by simpa only [e21] using hp 20 21 (by decide) (by decide))
        have e24 : c 24 = 2 := force2 _
          (by simpa only [e22] using hp 24 22 (by decide) (by decide))
          (by simpa only [e15] using hp 24 15 (by decide) (by decide))
        have e25 : c 25 = 0 := force0 _
          (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          (by simpa only [e24] using hp 25 24 (by decide) (by decide))
        exact False.elim (impossible (c 26)
          (by simpa only [e25] using hp 26 25 (by decide) (by decide))
          (by simpa only [e23] using hp 26 23 (by decide) (by decide))
          (by simpa only [e21] using hp 26 21 (by decide) (by decide)))
      · exact False.elim (hp 7 2 (by decide) (by decide) (e7.trans e2.symm))
    · exact False.elim (hp 5 1 (by decide) (by decide) (e5.trans e1.symm))
    · have e6 : c 6 = 0 := force0 _
        (by simpa only [e1] using hp 6 1 (by decide) (by decide))
        (by simpa only [e5] using hp 6 5 (by decide) (by decide))
      rcases three (c 7) with e7 | e7 | e7
      · have e8 : c 8 = 1 := force1 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
        have e14 : c 14 = 1 := force1 _
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
          (by simpa only [e16] using hp 14 16 (by decide) (by decide))
        have e15 : c 15 = 2 := force2 _
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
        have e17 : c 17 = 0 := force0 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        have e24 : c 24 = 1 := force1 _
          (by simpa only [e17] using hp 24 17 (by decide) (by decide))
          (by simpa only [e15] using hp 24 15 (by decide) (by decide))
        have e22 : c 22 = 0 := force0 _
          (by simpa only [e24] using hp 22 24 (by decide) (by decide))
          (by simpa only [e15] using hp 22 15 (by decide) (by decide))
        have e13 : c 13 = 1 := force1 _
          (by simpa only [e22] using hp 13 22 (by decide) (by decide))
          (by simpa only [e5] using hp 13 5 (by decide) (by decide))
        have e11 : c 11 = 0 := force0 _
          (by simpa only [e13] using hp 11 13 (by decide) (by decide))
          (by simpa only [e4] using hp 11 4 (by decide) (by decide))
        have e12 : c 12 = 1 := force1 _
          (by simpa only [e11] using hp 12 11 (by decide) (by decide))
          (by simpa only [e4] using hp 12 4 (by decide) (by decide))
        have e23 : c 23 = 2 := force2 _
          (by simpa only [e22] using hp 23 22 (by decide) (by decide))
          (by simpa only [e13] using hp 23 13 (by decide) (by decide))
        have e21 : c 21 = 0 := force0 _
          (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          (by simpa only [e23] using hp 21 23 (by decide) (by decide))
        have e20 : c 20 = 2 := force2 _
          (by simpa only [e21] using hp 20 21 (by decide) (by decide))
          (by simpa only [e12] using hp 20 12 (by decide) (by decide))
        have e10 : c 10 = 0 := force0 _
          (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          (by simpa only [e20] using hp 10 20 (by decide) (by decide))
        have e9 : c 9 = 2 := force2 _
          (by simpa only [e10] using hp 9 10 (by decide) (by decide))
          (by simpa only [e3] using hp 9 3 (by decide) (by decide))
        have e18 : c 18 = 1 := force1 _
          (by simpa only [e10] using hp 18 10 (by decide) (by decide))
          (by simpa only [e9] using hp 18 9 (by decide) (by decide))
        have e19 : c 19 = 0 := force0 _
          (by simpa only [e18] using hp 19 18 (by decide) (by decide))
          (by simpa only [e9] using hp 19 9 (by decide) (by decide))
        have e25 : c 25 = 2 := force2 _
          (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          (by simpa only [e24] using hp 25 24 (by decide) (by decide))
        have e26 : c 26 = 1 := force1 _
          (by simpa only [e19] using hp 26 19 (by decide) (by decide))
          (by simpa only [e23] using hp 26 23 (by decide) (by decide))
        refine ⟨1, ?_⟩
        funext e
        fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e7, e8, e16, e14, e15, e17, e24, e22, e13, e11, e12, e23, e21, e20, e10, e9, e18, e19, e25, e26]
      · have e8 : c 8 = 0 := force0 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 2 := force2 _
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
        exact False.elim (impossible (c 16)
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e14] using hp 16 14 (by decide) (by decide)))
      · exact False.elim (hp 7 2 (by decide) (by decide) (e7.trans e2.symm))
  · have e4 : c 4 = 1 := force1 _
      (by simpa only [e0] using hp 4 0 (by decide) (by decide))
      (by simpa only [e3] using hp 4 3 (by decide) (by decide))
    rcases three (c 5) with e5 | e5 | e5
    · have e6 : c 6 = 2 := force2 _
        (by simpa only [e5] using hp 6 5 (by decide) (by decide))
        (by simpa only [e1] using hp 6 1 (by decide) (by decide))
      have e11 : c 11 = 2 := force2 _
        (by simpa only [e5] using hp 11 5 (by decide) (by decide))
        (by simpa only [e4] using hp 11 4 (by decide) (by decide))
      have e12 : c 12 = 0 := force0 _
        (by simpa only [e4] using hp 12 4 (by decide) (by decide))
        (by simpa only [e11] using hp 12 11 (by decide) (by decide))
      have e13 : c 13 = 1 := force1 _
        (by simpa only [e5] using hp 13 5 (by decide) (by decide))
        (by simpa only [e11] using hp 13 11 (by decide) (by decide))
      rcases three (c 7) with e7 | e7 | e7
      · have e8 : c 8 = 1 := force1 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 1 := force1 _
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
        have e15 : c 15 = 0 := force0 _
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
        have e17 : c 17 = 0 := force0 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        have e22 : c 22 = 2 := force2 _
          (by simpa only [e15] using hp 22 15 (by decide) (by decide))
          (by simpa only [e13] using hp 22 13 (by decide) (by decide))
        have e23 : c 23 = 0 := force0 _
          (by simpa only [e13] using hp 23 13 (by decide) (by decide))
          (by simpa only [e22] using hp 23 22 (by decide) (by decide))
        have e24 : c 24 = 1 := force1 _
          (by simpa only [e15] using hp 24 15 (by decide) (by decide))
          (by simpa only [e22] using hp 24 22 (by decide) (by decide))
        have e25 : c 25 = 2 := force2 _
          (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          (by simpa only [e24] using hp 25 24 (by decide) (by decide))
        have e26 : c 26 = 1 := force1 _
          (by simpa only [e23] using hp 26 23 (by decide) (by decide))
          (by simpa only [e25] using hp 26 25 (by decide) (by decide))
        have e19 : c 19 = 0 := force0 _
          (by simpa only [e26] using hp 19 26 (by decide) (by decide))
          (by simpa only [e25] using hp 19 25 (by decide) (by decide))
        have e9 : c 9 = 1 := force1 _
          (by simpa only [e19] using hp 9 19 (by decide) (by decide))
          (by simpa only [e3] using hp 9 3 (by decide) (by decide))
        have e10 : c 10 = 0 := force0 _
          (by simpa only [e9] using hp 10 9 (by decide) (by decide))
          (by simpa only [e3] using hp 10 3 (by decide) (by decide))
        have e18 : c 18 = 2 := force2 _
          (by simpa only [e10] using hp 18 10 (by decide) (by decide))
          (by simpa only [e9] using hp 18 9 (by decide) (by decide))
        have e20 : c 20 = 1 := force1 _
          (by simpa only [e10] using hp 20 10 (by decide) (by decide))
          (by simpa only [e18] using hp 20 18 (by decide) (by decide))
        have e21 : c 21 = 2 := force2 _
          (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          (by simpa only [e20] using hp 21 20 (by decide) (by decide))
        refine ⟨2, ?_⟩
        funext e
        fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e11, e12, e13, e7, e8, e14, e15, e16, e17, e22, e23, e24, e25, e26, e19, e9, e10, e18, e20, e21]
      · have e8 : c 8 = 0 := force0 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 0 := force0 _
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
        have e15 : c 15 = 1 := force1 _
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
        have e17 : c 17 = 1 := force1 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        rcases three (c 9) with e9 | e9 | e9
        · have e10 : c 10 = 1 := force1 _
            (by simpa only [e9] using hp 10 9 (by decide) (by decide))
            (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          have e18 : c 18 = 2 := force2 _
            (by simpa only [e9] using hp 18 9 (by decide) (by decide))
            (by simpa only [e10] using hp 18 10 (by decide) (by decide))
          exact False.elim (impossible (c 20)
            (by simpa only [e12] using hp 20 12 (by decide) (by decide))
            (by simpa only [e10] using hp 20 10 (by decide) (by decide))
            (by simpa only [e18] using hp 20 18 (by decide) (by decide)))
        · have e10 : c 10 = 0 := force0 _
            (by simpa only [e9] using hp 10 9 (by decide) (by decide))
            (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          have e18 : c 18 = 2 := force2 _
            (by simpa only [e10] using hp 18 10 (by decide) (by decide))
            (by simpa only [e9] using hp 18 9 (by decide) (by decide))
          have e19 : c 19 = 0 := force0 _
            (by simpa only [e9] using hp 19 9 (by decide) (by decide))
            (by simpa only [e18] using hp 19 18 (by decide) (by decide))
          have e20 : c 20 = 1 := force1 _
            (by simpa only [e10] using hp 20 10 (by decide) (by decide))
            (by simpa only [e18] using hp 20 18 (by decide) (by decide))
          have e21 : c 21 = 2 := force2 _
            (by simpa only [e12] using hp 21 12 (by decide) (by decide))
            (by simpa only [e20] using hp 21 20 (by decide) (by decide))
          have e23 : c 23 = 0 := force0 _
            (by simpa only [e13] using hp 23 13 (by decide) (by decide))
            (by simpa only [e21] using hp 23 21 (by decide) (by decide))
          have e22 : c 22 = 2 := force2 _
            (by simpa only [e23] using hp 22 23 (by decide) (by decide))
            (by simpa only [e13] using hp 22 13 (by decide) (by decide))
          have e24 : c 24 = 0 := force0 _
            (by simpa only [e15] using hp 24 15 (by decide) (by decide))
            (by simpa only [e22] using hp 24 22 (by decide) (by decide))
          have e25 : c 25 = 2 := force2 _
            (by simpa only [e19] using hp 25 19 (by decide) (by decide))
            (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          have e26 : c 26 = 1 := force1 _
            (by simpa only [e19] using hp 26 19 (by decide) (by decide))
            (by simpa only [e21] using hp 26 21 (by decide) (by decide))
          refine ⟨3, ?_⟩
          funext e
          fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e11, e12, e13, e7, e8, e14, e15, e16, e17, e9, e10, e18, e19, e20, e21, e23, e22, e24, e25, e26]
        · exact False.elim (hp 9 3 (by decide) (by decide) (e9.trans e3.symm))
      · exact False.elim (hp 7 2 (by decide) (by decide) (e7.trans e2.symm))
    · exact False.elim (hp 5 1 (by decide) (by decide) (e5.trans e1.symm))
    · have e6 : c 6 = 0 := force0 _
        (by simpa only [e1] using hp 6 1 (by decide) (by decide))
        (by simpa only [e5] using hp 6 5 (by decide) (by decide))
      have e11 : c 11 = 0 := force0 _
        (by simpa only [e4] using hp 11 4 (by decide) (by decide))
        (by simpa only [e5] using hp 11 5 (by decide) (by decide))
      have e12 : c 12 = 2 := force2 _
        (by simpa only [e11] using hp 12 11 (by decide) (by decide))
        (by simpa only [e4] using hp 12 4 (by decide) (by decide))
      have e13 : c 13 = 1 := force1 _
        (by simpa only [e11] using hp 13 11 (by decide) (by decide))
        (by simpa only [e5] using hp 13 5 (by decide) (by decide))
      rcases three (c 7) with e7 | e7 | e7
      · have e8 : c 8 = 1 := force1 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e16 : c 16 = 2 := force2 _
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
        have e14 : c 14 = 1 := force1 _
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
          (by simpa only [e16] using hp 14 16 (by decide) (by decide))
        have e15 : c 15 = 2 := force2 _
          (by simpa only [e6] using hp 15 6 (by decide) (by decide))
          (by simpa only [e14] using hp 15 14 (by decide) (by decide))
        have e17 : c 17 = 0 := force0 _
          (by simpa only [e8] using hp 17 8 (by decide) (by decide))
          (by simpa only [e16] using hp 17 16 (by decide) (by decide))
        have e22 : c 22 = 0 := force0 _
          (by simpa only [e13] using hp 22 13 (by decide) (by decide))
          (by simpa only [e15] using hp 22 15 (by decide) (by decide))
        have e23 : c 23 = 2 := force2 _
          (by simpa only [e22] using hp 23 22 (by decide) (by decide))
          (by simpa only [e13] using hp 23 13 (by decide) (by decide))
        have e24 : c 24 = 1 := force1 _
          (by simpa only [e17] using hp 24 17 (by decide) (by decide))
          (by simpa only [e15] using hp 24 15 (by decide) (by decide))
        have e25 : c 25 = 2 := force2 _
          (by simpa only [e17] using hp 25 17 (by decide) (by decide))
          (by simpa only [e24] using hp 25 24 (by decide) (by decide))
        rcases three (c 9) with e9 | e9 | e9
        · have e10 : c 10 = 1 := force1 _
            (by simpa only [e9] using hp 10 9 (by decide) (by decide))
            (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          have e18 : c 18 = 2 := force2 _
            (by simpa only [e9] using hp 18 9 (by decide) (by decide))
            (by simpa only [e10] using hp 18 10 (by decide) (by decide))
          have e19 : c 19 = 1 := force1 _
            (by simpa only [e9] using hp 19 9 (by decide) (by decide))
            (by simpa only [e18] using hp 19 18 (by decide) (by decide))
          have e20 : c 20 = 0 := force0 _
            (by simpa only [e10] using hp 20 10 (by decide) (by decide))
            (by simpa only [e12] using hp 20 12 (by decide) (by decide))
          have e21 : c 21 = 1 := force1 _
            (by simpa only [e20] using hp 21 20 (by decide) (by decide))
            (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          have e26 : c 26 = 0 := force0 _
            (by simpa only [e19] using hp 26 19 (by decide) (by decide))
            (by simpa only [e23] using hp 26 23 (by decide) (by decide))
          refine ⟨4, ?_⟩
          funext e
          fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e11, e12, e13, e7, e8, e16, e14, e15, e17, e22, e23, e24, e25, e9, e10, e18, e19, e20, e21, e26]
        · have e10 : c 10 = 0 := force0 _
            (by simpa only [e9] using hp 10 9 (by decide) (by decide))
            (by simpa only [e3] using hp 10 3 (by decide) (by decide))
          have e18 : c 18 = 2 := force2 _
            (by simpa only [e10] using hp 18 10 (by decide) (by decide))
            (by simpa only [e9] using hp 18 9 (by decide) (by decide))
          have e19 : c 19 = 0 := force0 _
            (by simpa only [e9] using hp 19 9 (by decide) (by decide))
            (by simpa only [e18] using hp 19 18 (by decide) (by decide))
          have e20 : c 20 = 1 := force1 _
            (by simpa only [e10] using hp 20 10 (by decide) (by decide))
            (by simpa only [e12] using hp 20 12 (by decide) (by decide))
          have e21 : c 21 = 0 := force0 _
            (by simpa only [e20] using hp 21 20 (by decide) (by decide))
            (by simpa only [e12] using hp 21 12 (by decide) (by decide))
          have e26 : c 26 = 1 := force1 _
            (by simpa only [e19] using hp 26 19 (by decide) (by decide))
            (by simpa only [e23] using hp 26 23 (by decide) (by decide))
          refine ⟨5, ?_⟩
          funext e
          fin_cases e <;> simp [samples, e0, e1, e2, e3, e4, e5, e6, e11, e12, e13, e7, e8, e16, e14, e15, e17, e22, e23, e24, e25, e9, e10, e18, e19, e20, e21, e26]
        · exact False.elim (hp 9 3 (by decide) (by decide) (e9.trans e3.symm))
      · have e8 : c 8 = 0 := force0 _
          (by simpa only [e7] using hp 8 7 (by decide) (by decide))
          (by simpa only [e2] using hp 8 2 (by decide) (by decide))
        have e14 : c 14 = 2 := force2 _
          (by simpa only [e6] using hp 14 6 (by decide) (by decide))
          (by simpa only [e7] using hp 14 7 (by decide) (by decide))
        exact False.elim (impossible (c 16)
          (by simpa only [e8] using hp 16 8 (by decide) (by decide))
          (by simpa only [e7] using hp 16 7 (by decide) (by decide))
          (by simpa only [e14] using hp 16 14 (by decide) (by decide)))
      · exact False.elim (hp 7 2 (by decide) (by decide) (e7.trans e2.symm))


/-- Adjacency of edges in the subgraph omitting one colour. -/
def TwoColorAdj (c : Coloring) (omitted : Fin 3) (e f : Edge) : Prop :=
  Touch ends e f ∧ c e ≠ omitted ∧ c f ≠ omitted
  deriving Decidable

/-- Connectivity in one two-colour subgraph. Its absence also rules out
a common bichromatic cycle, not arbitrary uncoloured even cycles. -/
def Joined (c : Coloring) : Prop :=
  ∃ omitted, Relation.ReflTransGen (TwoColorAdj c omitted) 8 9

private def separatorMasks : Fin 6 → Fin 3 → Nat := ![
  ![82246,256,49208747],
  ![125952294,256,91127243],
  ![82246,256,16957824],
  ![256,65887597,16957824],
  ![61732158,256,21129683],
  ![125952294,256,21129683]]

private def inside (i : Fin 6) (t : Fin 3) (e : Edge) : Bool :=
  (separatorMasks i t).testBit e.val

/-- These small cuts are checked, not trusted connectivity outputs. -/
private theorem separators_correct : ∀ i t,
    inside i t 8 = true ∧ inside i t 9 = false ∧
    ∀ e f, inside i t e = true → TwoColorAdj (samples i) t e f →
      inside i t f = true := by decide +kernel

theorem samples_not_joined (i : Fin 6) : ¬ Joined (samples i) := by
  rintro ⟨t, h⟩
  have hc := separators_correct i t
  have closed {e f} (walk : Relation.ReflTransGen (TwoColorAdj (samples i) t) e f) :
      inside i t e = true → inside i t f = true := by
    induction walk with
    | refl => exact id
    | @tail b d _ step ih =>
        intro he
        exact hc.2.2 b d (ih he) step
  have hf := closed h hc.1
  rw [hc.2.1] at hf
  contradiction

private def anchor (i : Fin 3) : Edge := ⟨i.val, by omega⟩

private theorem anchor_data : Function.Injective anchor ∧
    ∀ i j, Touch ends (anchor i) (anchor j) := by decide +kernel

theorem exists_normalization (c : Coloring) (hp : Proper ends c) :
    ∃ (σ : Fin 3 ≃ Fin 3) (i : Fin 6), σ.symm ∘ c = samples i := by
  have hinj : Function.Injective (fun i => c (anchor i)) := by
    intro i j heq
    by_contra hne
    exact hp _ _ (anchor_data.1.ne hne) (anchor_data.2 i j) heq
  let σ : Fin 3 ≃ Fin 3 := Equiv.ofBijective (fun i => c (anchor i))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, rfl⟩)
  have hproper : Proper ends (σ.symm ∘ c) := by
    intro e f hne ht heq
    exact hp e f hne ht (σ.symm.injective heq)
  have hanchor (i : Fin 3) : σ.symm (c (anchor i)) = i :=
    σ.symm_apply_apply i
  obtain ⟨i, hi⟩ := normalized_cases (σ.symm ∘ c) hproper
    (hanchor 0) (hanchor 1) (hanchor 2)
  exact ⟨σ, i, hi⟩

/-- No choice of colouring, not merely no choice in one Kempe orbit, gives
a common bichromatic component through the two designated edges. -/
theorem no_coloring_joins (c : Coloring) (hp : Proper ends c) : ¬ Joined c := by
  rintro ⟨t, h⟩
  obtain ⟨σ, i, hi⟩ := exists_normalization c hp
  apply samples_not_joined i
  refine ⟨σ.symm t, ?_⟩
  rw [← hi]
  apply Relation.ReflTransGen.mono (r := TwoColorAdj c t) _ h
  intro e f hs
  exact ⟨hs.1, fun he => hs.2.1 (σ.symm.injective he),
    fun hf => hs.2.2 (σ.symm.injective hf)⟩

/-- The universal failure is non-vacuous. -/
theorem colorable_but_never_joined :
    (∃ c, Proper ends c) ∧ ¬ ∃ c, Proper ends c ∧ Joined c :=
  ⟨⟨samples 0, samples_proper 0⟩,
    fun ⟨c, hp, hj⟩ => no_coloring_joins c hp hj⟩

end Mettapedia.GraphTheory.FourColor.SmoothingCycleObstruction
