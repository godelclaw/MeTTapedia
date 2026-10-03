import MettapediaFourColor.FiveTriangleJointChoice
import Mettapedia.GraphTheory.FourColor.KempePaletteRigidity

/-!
# A fixed seam that no Kempe history repairs

Attach a decagon fan to D0092 after bypassing boundary vertex 6 (zero-based).
The displayed colouring has one connected support for each pair of colours.
Every physical Kempe history therefore only renames its colours. Both
orientations of the retained interface force a two-coloured triangle in D0063.
Another colouring of the same source and exterior does reconstruct. Thus the
obstruction concerns repair from a prescribed state with this seam retained.
-/

namespace FourColor.FiveTriangleKempeTrap

open Color FiveTriangleCollapseObstruction
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
open Mettapedia.GraphTheory.FourColor.KempePaletteRigidity

set_option maxRecDepth 32768

/-- Fan at source vertex 2; bypass the omitted vertex 6 by edge {5,7}. -/
def exterior : List (Fin 18 × Fin 18) :=
  [(5, 7), (2, 4), (2, 5), (2, 7), (2, 8), (2, 9), (2, 10), (2, 0)]

def graph := upper.graph ⊔ FiveTriangleJointChoice.edgeGraph exterior
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

def ports : Bool → Fin 10 → Fin 18
  | false => ![2, 3, 4, 5, 7, 8, 9, 10, 0, 1]
  | true => ![2, 1, 0, 10, 9, 8, 7, 5, 4, 3]

/-- Both orientations retain exactly the same fan on ten distinct ports. -/
theorem fan_exact : ∀ reverse, Function.Injective (ports reverse) ∧ ∀ i j : Fin 10,
    (graph.Adj (ports reverse i) (ports reverse j) ↔ FiveTriangleJointChoice.fanAdj i j) := by
  decide +kernel

def assignment : Fin 18 → Color :=
  ![c0, c1, c2, c1, c0, c1, c0, c3, c1, c3, c1, c2, c3, c2, c0, c0, c0, c3]

theorem assignment_proper : ∀ u v, graph.Adj u v → assignment u ≠ assignment v := by
  decide +kernel

def base : graph.Coloring Color := .mk assignment (fun h => assignment_proper _ _ h)

/-- Six short walks, one for each unordered pair of distinct colours. -/
def chains : Fin 6 → List (Fin 18) := ![
    [0, 1, 15, 3, 4, 5, 6, 5, 4, 3, 15, 1, 0, 10, 16, 8, 14, 8, 16, 10, 0],
    [0, 2, 4, 2, 15, 11, 14, 13, 6, 13, 14, 11, 16, 11, 15, 2, 0],
    [0, 17, 15, 12, 4, 12, 14, 7, 6, 7, 14, 12, 15, 17, 16, 9, 16, 17, 0],
    [1, 2, 3, 2, 5, 13, 5, 2, 8, 11, 8, 2, 10, 2, 1],
    [1, 17, 10, 9, 8, 7, 5, 12, 3, 12, 5, 7, 8, 9, 10, 17, 1],
    [2, 7, 13, 12, 11, 17, 11, 12, 13, 7, 2, 9, 2]]

def chain (a b : Color) : List (Fin 18) :=
  if (a = c0 ∧ b = c1) ∨ (a = c1 ∧ b = c0) then chains 0
  else if (a = c0 ∧ b = c2) ∨ (a = c2 ∧ b = c0) then chains 1
  else if (a = c0 ∧ b = c3) ∨ (a = c3 ∧ b = c0) then chains 2
  else if (a = c1 ∧ b = c2) ∨ (a = c2 ∧ b = c1) then chains 3
  else if (a = c1 ∧ b = c3) ∨ (a = c3 ∧ b = c1) then chains 4
  else chains 5

theorem chains_connected : ∀ a b, a ≠ b → (chain a b).IsChain graph.Adj := by
  decide +kernel

theorem chains_exact : ∀ a b, a ≠ b → ∀ v,
    v ∈ chain a b ↔ assignment v = a ∨ assignment v = b := by decide +kernel

/-- The invariant is a global palette orbit, not a table of repair histories. -/
theorem history_only_renames {C : graph.Coloring Color} (p : History base C) :
    PaletteOrbit assignment C :=
  history_paletteOrbit assignment chain chains_connected chains_exact p
    ⟨Equiv.refl _, fun _ => rfl⟩

def boundaryColours : Fin 10 → Color :=
  ![c2, c1, c0, c1, c3, c1, c3, c1, c0, c1]

theorem boundary_same : ∀ reverse i, assignment (ports reverse i) = boundaryColours i := by
  decide +kernel

private theorem two_colour_triangle (x y a b c : Color) (hxy : x ≠ y)
    (ax : a ≠ x) (ay : a ≠ y) (bx : b ≠ x) (by' : b ≠ y)
    (cx : c ≠ x) (cy : c ≠ y) (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a) : False := by
  revert hxy ax ay bx by' cx cy ab bc ca
  revert y a b c
  cases x <;> decide +kernel

/-- Compatibility requires genuine target vertex colours, with a shared
palette and either orientation of the chosen seam. -/
def Compatible (C : graph.Coloring Color) : Prop :=
  ∃ reverse, ∃ k : lower.graph.Coloring Color,
    ∀ i : Fin 10, C (ports reverse i) = k (i.castAdd 7)

theorem orbit_incompatible {C : graph.Coloring Color} (hC : PaletteOrbit assignment C) :
    ¬ Compatible C := by
  obtain ⟨π, hC⟩ := hC
  rintro ⟨reverse, k, hk⟩
  have hb (i : Fin 10) : k (i.castAdd 7) = π (boundaryColours i) := by
    rw [← hk i, hC, boundary_same]
  have h3 : k 3 = π c1 := hb 3
  have h4 : k 4 = π c3 := hb 4
  have h5 : k 5 = π c1 := hb 5
  have h6 : k 6 = π c3 := hb 6
  have h7 : k 7 = π c1 := hb 7
  apply two_colour_triangle (π c1) (π c3) (k 11) (k 12) (k 14) (π.injective.ne (by decide))
  · rw [← h3]; exact k.valid (by decide +kernel)
  · rw [← h4]; exact k.valid (by decide +kernel)
  · rw [← h5]; exact k.valid (by decide +kernel)
  · rw [← h4]; exact k.valid (by decide +kernel)
  · rw [← h7]; exact k.valid (by decide +kernel)
  · rw [← h6]; exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)
  · exact k.valid (by decide +kernel)

/-- No finite sequence of actual whole-component switches can repair this
state through either orientation of the retained seam. -/
theorem no_history_repairs {C : graph.Coloring Color} (p : History base C) :
    ¬ Compatible C := orbit_incompatible (history_only_renames p)

/-- The same obstruction holds for the library's ordinary Kempe closure. -/
theorem no_kempe_closure_repairs {C : graph.Coloring Color} (h : C ∈ graph.KempeClosure base) :
    ¬ Compatible C := by
  obtain ⟨p⟩ := nonempty_history_iff.mpr h
  exact no_history_repairs p

def goodSource : Fin 18 → Color :=
  ![c0, c3, c1, c3, c2, c3, c1, c0, c2, c3, c2, c3, c0, c2, c1, c2, c0, c1]
def goodTarget : Fin 17 → Color :=
  ![c1, c3, c2, c3, c0, c2, c3, c2, c0, c3, c1, c2, c1, c2, c0, c1, c0]

theorem good_proper : (∀ u v, graph.Adj u v → goodSource u ≠ goodSource v) ∧
    (∀ u v, FiveTriangleJointChoice.targetGraph.Adj u v → goodTarget u ≠ goodTarget v) ∧
    (∀ i : Fin 10, goodSource (ports false i) = goodTarget (i.castAdd 7)) := by
  decide +kernel

def goodColouring : graph.Coloring Color := .mk goodSource (fun h => good_proper.1 _ _ h)

/-- A different starting choice works in precisely the same exterior. -/
theorem another_choice_works : Compatible goodColouring := by
  refine ⟨false, .mk goodTarget (fun {u v} h => good_proper.2.1 u v (Or.inl h)), ?_⟩
  exact good_proper.2.2

end FourColor.FiveTriangleKempeTrap
