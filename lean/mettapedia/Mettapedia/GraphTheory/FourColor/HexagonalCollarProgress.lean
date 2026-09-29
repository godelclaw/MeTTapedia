import Mettapedia.GraphTheory.FourColor.HexagonalCollar
import Mettapedia.GraphTheory.FourColor.HexagonalTubeReduction

/-!
# Bounded geometric alternatives while growing hexagonal collars

In a map whose faces are pentagons or hexagons, a recognized row has a
specific next row unless an incident face is pentagonal or two face-derived
candidate vertices collide. Repeating successful checks constructs actual
hexagonal tubes, hence consumes their physical reduction. A least
counterexample must expose one of the two obstructions within three
successful extensions of any recognized five-port row.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab

open ZigzagRing PhysicalForkCodeFaces GoertzelV24TwoEdgeCutMinimality

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {inner : V → Prop} (S : ZigzagSlab RS k inner)

/-- These are literal face sizes and equalities of original vertices. -/
def CollarObstruction : Prop :=
  (∃ i : Fin k, (RS.faceOrbit (S.ι (.inr (.inr i)))).card = 5) ∨
    ∃ v w : Vtx k, v ≠ w ∧ S.collarVertex v = S.collarVertex w

variable (hC : Cubic3 RS)
  (hfaces : ∀ d : RS.D, (RS.faceOrbit d).card = 5 ∨ (RS.faceOrbit d).card = 6)

include hfaces in
theorem collarShortFaces_of_all : S.CollarShortFaces := fun _ => hfaces _

include hfaces in
theorem clean_of_no_obstruction (h : ¬ S.CollarObstruction) :
    S.HexagonalSeam ∧ Function.Injective S.collarVertex := by
  constructor
  · intro i
    rcases hfaces (S.ι (.inr (.inr i))) with hp | hh
    · exact (h (Or.inl ⟨i, hp⟩)).elim
    · exact hh
  · intro v w he
    by_contra hn
    exact h (Or.inr ⟨v, w, hn, he⟩)

/-- Inspect this row, then at most `n` canonically constructed successors.
The recursive step retains the exact collar geometry and both interfaces. -/
def StopsWithin : {inner : V → Prop} → (S : ZigzagSlab RS k inner) →
    S.RotationCompatible → ℕ → Prop
  | _, S, _, 0 => S.CollarObstruction
  | _, S, hS, n + 1 => S.CollarObstruction ∨
      ∃ (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex),
        StopsWithin (S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces))
          (S.nextRow_rotation hC hS hh hv (S.collarShortFaces_of_all hfaces)) n

/-- Failure to meet an obstruction supplies the entire longer tube, rather
than only a sequence of boundary relations. -/
theorem tube_of_not_stops (hS : S.RotationCompatible) (n : ℕ)
    (hn : ¬ StopsWithin hC hfaces S hS n) :
    ∃ t : Tube RS k inner (n + 2), t.Hexagonal := by
  induction n generalizing inner with
  | zero =>
    obtain ⟨hh, hv⟩ := S.clean_of_no_obstruction hfaces hn
    let T := S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces)
    have hT : T.RotationCompatible := S.nextRow_rotation hC hS hh hv _
    exact ⟨.cons S (.cons T (.nil _ T.outEquiv)), ⟨hS, hh, hT, rfl, trivial⟩⟩
  | succ n ih =>
    have hbad : ¬ S.CollarObstruction := fun h => hn (Or.inl h)
    obtain ⟨hh, hv⟩ := S.clean_of_no_obstruction hfaces hbad
    let T := S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces)
    have hT : T.RotationCompatible := S.nextRow_rotation hC hS hh hv _
    have hnext : ¬ StopsWithin hC hfaces T hT n := fun h => hn (Or.inr ⟨hh, hv, h⟩)
    obtain ⟨t, ht⟩ := ih T hT hnext
    refine ⟨.cons S t, hS, ?_, ht⟩
    cases t
    exact hh

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Every supplied five-port row of a minimal counterexample encounters a
pentagonal seam face or a genuine candidate-vertex collision within three
successful collar extensions. Neither alternative is assumed reducible. -/
theorem stopsWithin_three (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem 5 inner)
    (hS : S.RotationCompatible) :
    StopsWithin (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic)
      faces S hS 3 := by
  by_contra h
  obtain ⟨t, ht⟩ := S.tube_of_not_stops
    (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic) faces hS 3 h
  have := t.hexagonal_five_length_le_four rotation minimal ht
  omega

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab
