import MettapediaFourColor.ThreeBlockCore
import Mettapedia.GraphTheory.Kempe.PairHistory

/-!
# An extra changed port blocks every following zero/two phase

Switching the one/two component at port two need not change that port alone.
If it changes exactly ports two and four on the boundary, the resulting word
cannot be repaired by any sequence of zero/two component switches. The two active boundary runs each
retain one Boolean choice. None of their four joint choices extends to the
source core, as five forced core colours show.

The obstruction concerns this restricted strategy, not arbitrary mixed-pair
repair. The separate finite consumer exhibits a successful alternative.
-/

namespace FourColor.PortPreparationObstruction

open SimpleGraph Color ThreeBlockCore FiveTriangleCollapseObstruction

def word (b c : Bool) : Fin 11 → Color :=
  ![c1,c3,c1,c3,bitColour (!b),bitColour b,c3,
    bitColour c,bitColour (!c),bitColour c,bitColour (!c)]

private theorem fourth (b : Bool) (x : Color)
    (h0 : x ≠ bitColour b) (h2 : x ≠ bitColour (!b)) (h3 : x ≠ c3) : x = c1 := by
  revert h0 h2 h3
  cases b <;> cases x <;> decide

private theorem third (b : Bool) (x : Color)
    (h0 : x ≠ bitColour b) (h2 : x ≠ bitColour (!b)) (h1 : x ≠ c1) : x = c3 := by
  revert h0 h2 h1
  cases b <;> cases x <;> decide

private theorem remaining (b : Bool) (x : Color)
    (h1 : x ≠ c1) (h3 : x ≠ c3) (hb : x ≠ bitColour b) :
    x = bitColour (!b) := by
  revert h1 h3 hb
  cases b <;> cases x <;> decide

/-- The core rejects all joint choices, without a boundary-colouring table. -/
theorem no_extension (b c : Bool) (K : upper.graph.Coloring Color)
    (boundary : ∀ j : Fin 11, K (j.castAdd 7) = word b c j) : False := by
  have edge (u v : Fin 18) (h : upper.graph.Adj u v) : K u ≠ K v := K.valid h
  have b0 := boundary 0
  have b1 := boundary 1
  have b2 := boundary 2
  have b3 := boundary 3
  have b4 := boundary 4
  have b5 := boundary 5
  have b7 := boundary 7
  have b8 := boundary 8
  have b10 := boundary 10
  change K 0 = c1 at b0
  change K 1 = c3 at b1
  change K 2 = c1 at b2
  change K 3 = c3 at b3
  change K 4 = bitColour (!b) at b4
  change K 5 = bitColour b at b5
  change K 7 = bitColour c at b7
  change K 8 = bitColour (!c) at b8
  change K 10 = bitColour (!c) at b10
  have k12 : K 12 = c1 := fourth b (K 12)
    (b5 ▸ edge 12 5 (by decide +kernel))
    (b4 ▸ edge 12 4 (by decide +kernel))
    (b3 ▸ edge 12 3 (by decide +kernel))
  have k17 : K 17 = bitColour c := by
    simpa using remaining (!c) (K 17)
      (b0 ▸ edge 17 0 (by decide +kernel))
      (b1 ▸ edge 17 1 (by decide +kernel))
      (b10 ▸ edge 17 10 (by decide +kernel))
  have k15 : K 15 = bitColour (!c) := remaining c (K 15)
    (b2 ▸ edge 15 2 (by decide +kernel))
    (b1 ▸ edge 15 1 (by decide +kernel))
    (k17 ▸ edge 15 17 (by decide +kernel))
  have k11 : K 11 = c3 := third c (K 11)
    (k17 ▸ edge 11 17 (by decide +kernel))
    (k15 ▸ edge 11 15 (by decide +kernel))
    (k12 ▸ edge 11 12 (by decide +kernel))
  have k14 : K 14 = c1 := fourth c (K 14)
    (b7 ▸ edge 14 7 (by decide +kernel))
    (b8 ▸ edge 14 8 (by decide +kernel))
    (k11 ▸ edge 14 11 (by decide +kernel))
  exact edge 12 14 (by decide +kernel) (k12.trans k14.symm)

private theorem pair_choice (x : Color) (h : x = c0 ∨ x = c2) :
    ∃ b : Bool, x = bitColour b := by
  rcases h with h | h
  · exact ⟨false,h⟩
  · exact ⟨true,h⟩

private theorem opposite (b : Bool) (x : Color)
    (h : x = c0 ∨ x = c2) (ne : x ≠ bitColour b) : x = bitColour (!b) := by
  revert h ne
  cases b <;> cases x <;> decide

/-- Properness alone keeps each active boundary run alternating. This
holds for an arbitrary exterior and any length of the fixed-pair phase. -/
theorem phase_word {W : Type*} {H : SimpleGraph W}
    (D E : H.Coloring Color) (ports : Fin 11 → W)
    (boundary : ∀ j, D (ports j) = word false false j)
    (edge45 : H.Adj (ports 4) (ports 5))
    (edge78 : H.Adj (ports 7) (ports 8))
    (edge89 : H.Adj (ports 8) (ports 9))
    (edge910 : H.Adj (ports 9) (ports 10))
    (history : Relation.ReflTransGen (KempePairHistory.Step c0 c2) D E) :
    ∃ b c : Bool, ∀ j, E (ports j) = word b c j := by
  have pw := KempePairHistory.pointwise history
  have boundaryChoice (j : Fin 11) : E (ports j) = word false false j ∨
      E (ports j) = Equiv.swap c0 c2 (word false false j) := by
    simpa only [boundary] using pw (ports j)
  have active (j : Fin 11) (hj : j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10) :
      E (ports j) = c0 ∨ E (ports j) = c2 := by
    have h := boundaryChoice j
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [word,bitColour,or_comm] using h
  obtain ⟨b,hb⟩ := pair_choice _ (active 5 (by simp))
  obtain ⟨c,hc⟩ := pair_choice _ (active 7 (by simp))
  have h4 := opposite b _ (active 4 (by simp)) (hb ▸ E.valid edge45)
  have h8 := opposite c _ (active 8 (by simp)) (hc ▸ E.valid edge78.symm)
  have h9 : E (ports 9) = bitColour c := by
    simpa using opposite (!c) _ (active 9 (by simp)) (h8 ▸ E.valid edge89.symm)
  have h10 := opposite c _ (active 10 (by simp)) (h9 ▸ E.valid edge910.symm)
  refine ⟨b,c,?_⟩
  intro j
  fin_cases j
  · simpa [word, Equiv.swap_apply_def] using boundaryChoice 0
  · simpa [word, Equiv.swap_apply_def] using boundaryChoice 1
  · simpa [word, Equiv.swap_apply_def] using boundaryChoice 2
  · simpa [word, Equiv.swap_apply_def] using boundaryChoice 3
  · exact h4
  · exact hb
  · simpa [word, Equiv.swap_apply_def] using boundaryChoice 6
  · exact hc
  · exact h8
  · exact h9
  · exact h10

theorem no_tail_phase {W : Type*} {H : SimpleGraph W}
    (D E : H.Coloring Color) (ports : Fin 11 → W)
    (boundary : ∀ j, D (ports j) = word false false j)
    (edge45 : H.Adj (ports 4) (ports 5))
    (edge78 : H.Adj (ports 7) (ports 8))
    (edge89 : H.Adj (ports 8) (ports 9))
    (edge910 : H.Adj (ports 9) (ports 10))
    (history : Relation.ReflTransGen (KempePairHistory.Step c0 c2) D E)
    (K : upper.graph.Coloring Color)
    (agree : ∀ j : Fin 11, K (j.castAdd 7) = E (ports j)) : False := by
  obtain ⟨b,c,h⟩ := phase_word D E ports boundary edge45 edge78 edge89 edge910 history
  exact no_extension b c K (fun j => (agree j).trans (h j))

end FourColor.PortPreparationObstruction
