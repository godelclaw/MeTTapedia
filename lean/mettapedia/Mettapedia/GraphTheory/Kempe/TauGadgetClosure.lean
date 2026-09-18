import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

/-!
# Closure of the gadget's breadth-first components

For every listed gadget state, every listed colour pair and every seed edge,
one further layer of the breadth-first search `tauComponent` adds nothing: the
computed component is closed under two-coloured adjacency.  This is the finite
fact that makes the search complete; it is checked by `decide` in four
chunks.
-/

namespace Mettapedia.GraphTheory.Kempe.TauGadget

open Mettapedia.GraphTheory.FourColor
open GoertzelLemma814

/-- Whether every breadth-first component of the `i`-th state is closed. -/
def componentsClosedAt (i : Nat) : Bool :=
  colorPairs.all fun p => tauEdges.all fun seed =>
    (nextComponentLayer (stateAt i) p.1 p.2 (tauComponent (stateAt i) p.1 p.2 seed)).isEmpty

def componentsClosedRange (start len : Nat) : Bool :=
  (List.range len).all fun k => componentsClosedAt (start + k)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem componentsClosedRange_0_48 : componentsClosedRange 0 48 = true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem componentsClosedRange_48_48 : componentsClosedRange 48 48 = true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem componentsClosedRange_96_48 : componentsClosedRange 96 48 = true := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem componentsClosedRange_144_48 : componentsClosedRange 144 48 = true := by decide

theorem componentsClosedAt_of_lt {i : Nat} (hi : i < 192) : componentsClosedAt i = true := by
  have hrange (start len k : Nat) (h : componentsClosedRange start len = true) (hk : k < len) :
      componentsClosedAt (start + k) = true :=
    List.all_eq_true.1 h k (List.mem_range.2 hk)
  rcases (by omega : i < 48 ∨ (48 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 144) ∨ 144 ≤ i) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
  · simpa using hrange 0 48 i componentsClosedRange_0_48 h
  · simpa [Nat.add_sub_cancel' h1] using
      hrange 48 48 (i - 48) componentsClosedRange_48_48 (by omega)
  · simpa [Nat.add_sub_cancel' h1] using
      hrange 96 48 (i - 96) componentsClosedRange_96_48 (by omega)
  · simpa [Nat.add_sub_cancel' h1] using
      hrange 144 48 (i - 144) componentsClosedRange_144_48 (by omega)

end Mettapedia.GraphTheory.Kempe.TauGadget
