import MettapediaFourColor.KempeIntervalRepair
import MettapediaFourColor.TriangleStripAnchors
import MettapediaFourColor.KempeBoundarySplit

/-!
# Two source repairs requiring adaptive noncrossing chord choice

Four successful pair choices cover every noncrossing exterior matching.
They do not cover every crossing matching, and no single active anchor
has only successful possible partners. The interval theorem selects a
whole actual chord and its answer is an actual D0099 colouring.
-/

namespace FourColor.StripIntervalRepair

open Color KempeBoundarySplit KempeMatchingChromogram

def word : Bool → Fin 11 → Color
  | false => ![c1,c1,c1,c2,c1,c2,c2,c2,c2,c3,c1]
  | true => ![c1,c1,c1,c2,c1,c2,c3,c2,c2,c2,c1]

def pairs : Bool → List (Fin 11 × Fin 11)
  | false => [(3,5),(5,6),(6,7),(7,8)]
  | true => [(3,5),(3,9),(7,8),(8,9)]

def good (s : Bool) (a b : Fin 11) : Bool :=
  (pairs s).contains (min a b, max a b)

def data : Bool → String
  | false => "0101230202132311203010132120213120330201013203021232113020101320212130213302"
  | true => "0101230313120312203010123120213230120301013203031232113020101320312120213302"

def colour (s : Bool) (i : Fin 4) (v : Fin 19) : Color :=
  ![c0,c1,c2,c3] ⟨((data s).toUTF8[19 * i.val + v.val]?.getD 48).toNat % 4,
    Nat.mod_lt _ (by decide)⟩

theorem proper : ∀ s i u v, TriangleStripAnchors.input0099.graph.Adj u v →
    colour s i u ≠ colour s i v := by decide +kernel

def colouring (s : Bool) (i : Fin 4) : TriangleStripAnchors.input0099.graph.Coloring Color :=
  .mk (colour s i) (fun h => proper s i _ _ h)

theorem nonzero : ∀ s i, word s i ≠ 0 := by decide +kernel

theorem rejection : ∀ s,
    KempeIntervalMatching.possible (KempeIntervalRepair.active (word s))
      (KempeIntervalRepair.bad (good s)) 0 11 = false := by decide +kernel

theorem answers : ∀ s a b, good s a b = true → ∃ i : Fin 4,
    List.ofFn (KempeIntervalRepair.switch (word s) a b) =
      trace (TriangleStripAnchors.input0099.boundary.map (colour s i)) := by decide +kernel

/-- Three genuine noncrossing matchings witness different anchor failures. -/
def alternatives : Fin 3 → Fin 11 → Fin 11 :=
  ![![0,1,2,7,4,6,5,3,9,8,10],
    ![0,1,2,9,4,8,7,6,5,3,10],
    ![0,1,2,5,4,3,9,8,7,6,10]]

theorem alternatives_valid : ∀ s j,
    Function.Involutive (alternatives j) ∧ Noncrossing (alternatives j) ∧
      ∀ i, alternatives j i = i ↔ word s i = c1 := by
  unfold Function.Involutive
  decide +kernel

/-- No one active anchor covers all exteriors using the certified good pairs. -/
theorem no_fixed_anchor : ∀ s a, (word s a).hi = true →
    ∃ j : Fin 3, good s a (alternatives j a) = false := by decide +kernel

def crossingMate : Fin 11 → Fin 11 := ![0,1,2,7,4,8,9,3,5,6,10]

/-- Ignoring noncrossing admits a complete matching avoiding every good pair. -/
theorem crossing_obstruction : Function.Involutive crossingMate ∧
    ¬ Noncrossing crossingMate ∧ ∀ s,
      (∀ i, crossingMate i = i ↔ word s i = c1) ∧
      ∀ i, good s i (crossingMate i) = false := by
  unfold Function.Involutive
  decide +kernel

/-- The actual supplied matching chooses one of four full source witnesses.
The same chromogram is retained, so any exterior accepting its answers
accepts the reconstructed source trace. -/
theorem source_repair (s : Bool) (mate : Fin 11 → Fin 11)
    (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (hf : ∀ i, mate i = i ↔ word s i = c1) :
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      matchg [] (trace (TriangleStripAnchors.input0099.boundary.map k)) (gram mate (word s)) := by
  have terminal : ∀ a b, good s a b = true →
      GraphTrace TriangleStripAnchors.input0099.graph TriangleStripAnchors.input0099.boundary
        (List.ofFn (KempeIntervalRepair.switch (word s) a b)) := by
    intro a b h
    obtain ⟨i,hi⟩ := answers s a b h
    exact ⟨colouring s i,hi⟩
  obtain ⟨_, _, _, ⟨k, he⟩, hm⟩ := KempeIntervalRepair.answer (word s) (good s)
    _ terminal (rejection s) mate hinv hnc (nonzero s) hf
  exact ⟨k, he ▸ hm⟩

end FourColor.StripIntervalRepair
