import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

/-!
# Finite rigidity check for the pentagonal corona

The partial diagram retains both cycles and their five coupled spokes.
Every proposed collision reaches a locally separated pair in at most six
simultaneous rotations or internal edge reversals. The generic soundness
argument then applies to any triangle-free simple-graph realization.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaSeparation

open PartialCubicDartSeparation ElevenLobeSpokeOrder

abbrev Vertex := Fin 11 ⊕ Fin 5
abbrev Slot := Vertex × Fin 3

def rotate : Slot → Slot
  | (.inl i, s) => (.inl i, if reverseAt i then s - 1 else s + 1)
  | (.inr i, s) => (.inr i, s + 1)

def inwardIndex (i : Fin 11) (h : i.val % 2 = 1) : Fin 5 := ⟨i.val / 2, by omega⟩

def flip : Slot → Option Slot
  | (.inl i, 0) => if h : i.val % 2 = 1 then some (.inr (-inwardIndex i h), 1) else none
  | (.inl i, 1) => some (.inl (i - 1), 2)
  | (.inl i, 2) => some (.inl (i + 1), 1)
  | (.inr i, 0) => some (.inr (i + 1), 2)
  | (.inr i, 1) => some (.inl (inward (-i)), 0)
  | (.inr i, 2) => some (.inr (i - 1), 0)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def diagram : Diagram Vertex where
  rotate := rotate
  flip := flip
  flip_reverse := by decide

/-- This checks the 720 ordered pairs of distinct vertices and relative
star phases. Each successful search has a uniform semantic interpretation. -/
theorem separates_all : ∀ u v : Vertex, u ≠ v → ∀ s : Fin 3,
    diagram.separates 6 (u, 0) (v, s) = true := by decide

end Mettapedia.GraphTheory.FourColor.PentagonalCoronaSeparation
