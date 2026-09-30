import Mettapedia.GraphTheory.FourColor.HexagonalTwoRowWiringRecognition
import Mettapedia.GraphTheory.FourColor.HexagonalCollarProgress

/-!
# A constructed hexagonal successor supplies a strict two-row reduction

A single recognized row constructs its successor from actual seam faces.
The new input labels equal the original output labels, so serial assembly
realizes the literal two-row tube with no independently supplied occurrence
or seam permutation. Short ambient end faces then derive its exterior
conditions and supply the strict reduction.

In the five/six-face class a minimal counterexample therefore has a
pentagonal seam at every recognized row of width at least three. No initial
row or universal coverage assertion follows from this stopping theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData ZigzagRing
open PhysicalForkCodeFaces GoertzelV24TwoEdgeCutMinimality

noncomputable section
universe u
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
set_option backward.isDefEq.respectTransparency false
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {k : ℕ} [NeZero k]

namespace ZigzagSlab

variable (S : ZigzagSlab RS k inner) (hC : Cubic3 RS) (hS : S.RotationCompatible)
  (hh : S.HexagonalSeam) (hs : S.CollarShortFaces)

/-- The actual collar inherits its input order from the original row. -/
theorem successor_matching :
    S.asSlab.matching (S.hexagonalNextRow hC hS hh hs).asSlab = Equiv.refl (Fin k) := by
  change S.outEquiv.trans (S.hexagonalNextRow hC hS hh hs).inEquiv.symm = _
  unfold hexagonalNextRow
  rw [nextRow_inEquiv]
  exact S.outEquiv.self_trans_symm

/-- Both rows, with their actual darts and no auxiliary vertices. -/
def twoRowSlab : SlabOf RS (tube k 1).data inner :=
  S.asSlab.assembleWith (S.hexagonalNextRow hC hS hh hs).asSlab (Equiv.refl _)
    (S.successor_matching hC hS hh hs)

theorem twoRowSlab_input (i : Fin k) :
    (S.twoRowSlab hC hS hh hs).ι (.inr (.inl i)) = S.ι (.inr (.inl i)) :=
  S.asSlab.assembleWith_input _ _ _ i

theorem twoRowSlab_output (i : Fin k) :
    (S.twoRowSlab hC hS hh hs).ι (.inr (.inr i)) = S.collarDart (.inr (.inr i)) :=
  S.asSlab.assembleWith_output _ _ _ i

theorem twoRowSlab_rotation : (S.twoRowSlab hC hS hh hs).RotationCompatible :=
  S.asSlab.assembleWith_rotationCompatible _ _ _ hS
    (S.hexagonalNextRow_rotation hC hS hh hs)

/-- The constructed operation deletes exactly both rows. -/
theorem twoRowSlab_vertex_loss : Fintype.card V =
    Fintype.card {v : V // (S.twoRowSlab hC hS hh hs).outsideKeep v} + 4 * k :=
  (S.twoRowSlab hC hS hh hs).wire_vertex_loss

variable (faces : ∀ d : RS.D, (RS.faceOrbit d).card = 5 ∨ (RS.faceOrbit d).card = 6)

include faces in
theorem twoRowSlab_short_end_faces : (S.twoRowSlab hC hS hh hs).ShortEndFaces :=
  fun _ => faces _

/-- Start from one recognized row; the actual reduction is an output. -/
theorem constructed_two_row_reduction (hk : 3 ≤ k)
    (ambient : BridgelessSphericalCubicMapData RS) :
    let U := S.twoRowSlab hC hS hh hs
    let H := U.wireTwoShores (S.twoRowSlab_rotation hC hS hh hs)
      (S.twoRowSlab_short_end_faces hC hS hh hs faces) ambient.primalConnected
    Fintype.card {v : V // U.outsideKeep v} < Fintype.card V ∧
      BridgelessSphericalCubicMapData (U.wireShortened H) ∧
      (RotationSystemTaitColorable (U.wireShortened H) → RotationSystemTaitColorable RS) := by
  exact (S.twoRowSlab hC hS hh hs).wire_reduction_of_short_end_faces hk
    (S.twoRowSlab_rotation hC hS hh hs) (S.twoRowSlab_short_end_faces hC hS hh hs faces) ambient

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A hexagonal successor cannot occur in a minimal counterexample in this
face class. The two-row embedding and exterior conditions are constructed. -/
theorem no_hexagonal_seam (hk : 3 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem k inner)
    (hS : S.RotationCompatible) (hh : S.HexagonalSeam) : False := by
  let hC := cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic
  let hs := S.collarShortFaces_of_all faces
  exact SlabOf.no_two_row_short_end_faces hk rotation minimal (S.twoRowSlab hC hS hh hs)
    (S.twoRowSlab_rotation hC hS hh hs) (S.twoRowSlab_short_end_faces hC hS hh hs faces)

/-- The starting row itself has a pentagonal output seam: zero extensions. -/
theorem pentagonalSeam_of_minimal (hk : 3 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem k inner)
    (hS : S.RotationCompatible) : S.PentagonalSeam := by
  by_contra hp
  have hh : S.HexagonalSeam := by
    intro i
    rcases faces (S.ι (.inr (.inr i))) with hf | hf
    · exact (hp ⟨i, hf⟩).elim
    · exact hf
  exact S.no_hexagonal_seam hk rotation minimal faces hS hh

end ZigzagSlab

namespace Tube
variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Any longer recognized chain contains a forbidden first hexagonal seam.
This bound is uniform in width and length and uses no stabilization table. -/
theorem short_face_length_le_one (hk : 3 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} {n : ℕ} (t : Tube rotation.toRotationSystem k inner n)
    (ht : t.Hexagonal) : n ≤ 1 := by
  cases t with
  | nil => omega
  | cons S rest =>
    cases rest with
    | nil => omega
    | cons T tail =>
      exact (S.no_hexagonal_seam hk rotation minimal faces ht.1 ht.2.1).elim

end Tube
end
end Mettapedia.GraphTheory.FourColor.TubeSlab
