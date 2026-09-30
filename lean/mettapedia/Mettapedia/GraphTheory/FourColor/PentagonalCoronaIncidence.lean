import Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

/-!
# The two cycles traced by a pentagonal corona

The face-derived darts construct both cycle frames and their matching.
The sixteen traced vertices must be distinct, and the outer cycle must be
induced. These conditions concern actual vertices and adjacency, rather
than an assumed correspondence with the reducibility certificate.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open CubicCycleIncidence ElevenLobeSpokeOrder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaIncidenceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaIncidenceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

/-- The cycle traced from the six faces has no additional internal edge. -/
def OuterInduced : Prop := ∀ i j : Fin 11,
  G.Adj (outerVertex rotation root i) (outerVertex rotation root j) →
    j = i - 1 ∨ j = i + 1

theorem outerStar_injective (hC : Cubic3 rotation.toRotationSystem) (i : Fin 11) :
    Function.Injective (outerStar rotation root i) := by
  have h10 : rotation.vertexRotation (outerBase rotation root i) ≠ outerBase rotation root i :=
    hC.moves _
  have h21 : rotation.vertexRotation (rotation.vertexRotation (outerBase rotation root i)) ≠
      rotation.vertexRotation (outerBase rotation root i) := hC.moves _
  have h20 : rotation.vertexRotation (rotation.vertexRotation (outerBase rotation root i)) ≠
      outerBase rotation root i := by
    intro he
    have hh := congrArg rotation.vertexRotation he
    have hcube : ∀ d : G.Dart,
        rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d)) = d := hC.cube
    rw [hcube] at hh
    exact h10 hh.symm
  intro a b hab
  cases h : reverseAt i <;> fin_cases a <;> fin_cases b <;>
    simp only [outerStar, h, Bool.false_eq_true, ite_false, ite_true] at hab <;>
    first | rfl | exact (h10 hab).elim | exact (h10 hab.symm).elim |
      exact (h21 hab).elim | exact (h21 hab.symm).elim |
      exact (h20 hab).elim | exact (h20 hab.symm).elim

variable (hC : Cubic3 rotation.toRotationSystem)
  (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
  (hn : NeighborPeriods rotation root)

include hC hroot hn

theorem outerStar_next_snd (i : Fin 11) :
    (outerStar rotation root i 2).snd = outerVertex rotation root (i + 1) := by
  have he := congrArg (fun d : G.Dart => d.fst)
    (outerStar_edge rotation root hC hroot hn i)
  change (outerStar rotation root i 2).snd = (outerStar rotation root (i + 1) 1).fst at he
  simpa only [outerStar_fst] using he

theorem outerStar_prev_snd (i : Fin 11) :
    (outerStar rotation root i 1).snd = outerVertex rotation root (i - 1) := by
  have he := congrArg (fun d : G.Dart => d.snd)
    (outerStar_edge rotation root hC hroot hn (i - 1))
  simp only [sub_add_cancel] at he
  change (outerStar rotation root (i - 1) 2).fst = (outerStar rotation root i 1).snd at he
  simpa only [outerStar_fst] using he.symm

theorem outerStar_spoke_outside (hinduced : OuterInduced rotation root) (i j : Fin 11) :
    (outerStar rotation root i 0).snd ≠ outerVertex rotation root j := by
  intro he
  have ha := (outerStar rotation root i 0).adj
  rw [outerStar_fst, he] at ha
  rcases hinduced i j ha with hj | hj
  · have hd : outerStar rotation root i 0 = outerStar rotation root i 1 := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext ((outerStar_fst _ _ _ _).trans (outerStar_fst _ _ _ _).symm)
        (he.trans (hj ▸ (outerStar_prev_snd rotation root hC hroot hn i).symm))
    have := outerStar_injective rotation root hC i hd
    contradiction
  · have hd : outerStar rotation root i 0 = outerStar rotation root i 2 := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext ((outerStar_fst _ _ _ _).trans (outerStar_fst _ _ _ _).symm)
        (he.trans (hj ▸ (outerStar_next_snd rotation root hC hroot hn i).symm))
    have := outerStar_injective rotation root hC i hd
    contradiction

variable (hv : Function.Injective (tracedVertex rotation root))
  (hinduced : OuterInduced rotation root)

/-- The outer cycle is constructed from the facial arcs. -/
def outerFrame : Frame G 11 where
  vertex := ⟨outerVertex rotation root, fun i j he => Sum.inl.inj (hv he)⟩
  adjacent i := by
    have ha := (outerStar rotation root i 2).adj
    rwa [outerStar_fst, outerStar_next_snd rotation root hC hroot hn] at ha
  spoke i := (outerStar rotation root i 0).snd
  spoke_adjacent i := by
    have ha := (outerStar rotation root i 0).adj
    rwa [outerStar_fst] at ha
  spoke_outside := outerStar_spoke_outside rotation root hC hroot hn hinduced

theorem outerFrame_star (i : Fin 11) (s : Fin 3) :
    (outerFrame rotation root hC hroot hn hv hinduced).star i s =
      outerStar rotation root i s := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rw [Frame.star_fst, outerStar_fst]; rfl
  · fin_cases s
    · rfl
    · exact (outerStar_prev_snd rotation root hC hroot hn i).symm
    · exact (outerStar_next_snd rotation root hC hroot hn i).symm

omit hC hroot hn hv hinduced in
theorem spoke_at_inward (i : Fin 5) :
    (rotation.vertexRotation (center rotation root i)).snd =
      outerVertex rotation root (inward (-i)) := by
  fin_cases i <;> rfl

omit hC hn hinduced in
/-- The central cycle and its third edges also come from actual face darts. -/
def innerFrame : Frame G 5 where
  vertex := ⟨fun i => (center rotation root i).fst, fun i j he => Sum.inr.inj (hv he)⟩
  adjacent i := by
    have he := congrArg (fun d : G.Dart => d.fst) (center_step rotation root hroot i)
    have hs : (center rotation root i).snd = (center rotation root (i + 1)).fst := by
      change (rotation.vertexRotation (center rotation root i).symm).fst =
        (center rotation root (i + 1)).fst at he
      rw [rotation.vertexRotation_fst] at he
      exact he
    have ha := (center rotation root i).adj
    rw [hs] at ha
    exact ha
  spoke i := (rotation.vertexRotation (center rotation root i)).snd
  spoke_adjacent i := by
    have ha := (rotation.vertexRotation (center rotation root i)).adj
    rwa [rotation.vertexRotation_fst] at ha
  spoke_outside i j := by
    intro he
    rw [spoke_at_inward] at he
    have := hv (show tracedVertex rotation root (.inl (inward (-i))) =
      tracedVertex rotation root (.inr j) from he)
    contradiction

/-- The incidence and shared attachment permutation are conclusions of the
face traversal; no cycle correspondence is supplied. -/
def incidence : Incidence G where
  outer := outerFrame rotation root hC hroot hn hv hinduced
  inner := innerFrame rotation root hroot hv
  disjoint i j := by
    intro he
    have := hv (show tracedVertex rotation root (.inl i) = tracedVertex rotation root (.inr j)
      from he)
    contradiction
  matching := ⟨Neg.neg, Neg.neg, neg_neg, neg_neg⟩
  spoke := spoke_at_inward rotation root

theorem incidence_rotation (d : CycleBoundaryOrientation.Dart 11) :
    rotation.vertexRotation ((incidence rotation root hC hroot hn hv hinduced).outer.star d.1 d.2) =
      (incidence rotation root hC hroot hn hv hinduced).outer.star
        (CycleBoundaryOrientation.turn 11 reverseAt d).1
        (CycleBoundaryOrientation.turn 11 reverseAt d).2 := by
  change rotation.vertexRotation ((outerFrame rotation root hC hroot hn hv hinduced).star d.1 d.2) = _
  simp only [incidence, outerFrame_star]
  exact outerStar_rotation rotation root hC d

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
