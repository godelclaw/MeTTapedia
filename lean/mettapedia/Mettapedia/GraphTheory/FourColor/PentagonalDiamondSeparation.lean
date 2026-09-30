import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaImmersion

/-!
# The twelve-vertex core of four neighbouring pentagons

The central pentagon and three consecutive pentagonal neighbours determine
this partial cubic diagram. Its six missing reversals are boundary ports.
Simultaneous dart transport excludes all collisions except two pairs of
vertices; each remaining pair closes a genuine four-cycle. No face length
is specified on the other two sides of the central pentagon.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalDiamond

open PartialCubicDartSeparation

abbrev Vertex := Fin 12
abbrev Slot := Vertex × Fin 3

def flat (d : Slot) : Fin 36 := ⟨3 * d.1.val + d.2.val, by omega⟩
def unflat (i : Fin 36) : Slot := (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)

def flipCodes : String := "c@E@CH`FK@IN]LQ@OTZR@[@b^SVaMYdG\\XA_"

def flip (d : Slot) : Option Slot :=
  let n := (flipCodes.toUTF8[flat d |>.val]?.getD 64).toNat
  if n = 64 then none else some (unflat ⟨(n - 65) % 36, Nat.mod_lt _ (by decide)⟩)

def rotate (d : Slot) : Slot :=
  (d.1, if d.1.val < 7 ∧ d.1.val % 2 = 1 then d.2 - 1 else d.2 + 1)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def diagram : Diagram Vertex where
  rotate := rotate
  flip := flip
  flip_reverse := by decide

/-- These coordinates retain the original central darts and the seven
outer vertices between the first and last selected neighbouring faces. -/
def embed (v : Vertex) : PentagonalCoronaSeparation.Vertex :=
  if h : v.val < 7 then .inl ⟨v.val + 3, by omega⟩ else .inr ⟨v.val - 7, by omega⟩

def embedSlot (d : Slot) : PentagonalCoronaSeparation.Slot := (embed d.1, d.2)

theorem embed_injective : Function.Injective embed := by decide

theorem embed_rotate (d : Slot) :
    embedSlot (rotate d) = PentagonalCoronaSeparation.rotate (embedSlot d) := by
  revert d
  decide

/-- The four ordered exceptional pairs are independent of relative phase.
Their four-edge paths are treated geometrically below. -/
theorem separates_or_ends : ∀ u v : Vertex, u ≠ v → ∀ s : Fin 3,
    diagram.separates 5 (u, 0) (v, s) = true ∨
      (u = 0 ∧ v = 6) ∨ (u = 6 ∧ v = 0) ∨
      (u = 1 ∧ v = 5) ∨ (u = 5 ∧ v = 1) := by decide

variable {V : Type*} {G : SimpleGraph V} (F : Realization diagram G)

theorem first_last_ne (hf : Realization.FourCycleFree (G := G)) :
    F.vertex 0 ≠ F.vertex 6 :=
  F.ne_of_path_four hf (b := 11) (c := 7) (d := 8) (by decide) (by decide)
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))

theorem outer_ends_ne (hf : Realization.FourCycleFree (G := G)) :
    F.vertex 1 ≠ F.vertex 5 :=
  F.ne_of_path_four hf (b := 2) (c := 3) (d := 4) (by decide) (by decide)
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))

/-- One partial diagram embeds in every girth-at-least-five simple graph
realizing its local operations. No global source size occurs in the check. -/
theorem vertex_injective (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) : Function.Injective F.vertex := by
  intro u v he
  by_contra hn
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart (u, 0)) ((F.fst _).trans he)
  rcases separates_or_ends u v hn s with hh | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact F.separates_sound ht hh hs.symm
  · exact first_last_ne F hf he
  · exact first_last_ne F hf he.symm
  · exact outer_ends_ne F hf he
  · exact outer_ends_ne F hf he.symm

end Mettapedia.GraphTheory.FourColor.PentagonalDiamond
