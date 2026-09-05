import Mettapedia.GraphTheory.FourColor.Flower7Base
import Mettapedia.GraphTheory.FourColor.NgonCap

/-! The 7-gon cap's words are covered by the base or the certificate nodes (in chunks of
250 boundary numerals); with the base verification and the cap's disc check,
`false_of_certificate'` excludes the configuration. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace Flower7

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding ZigzagRing TubeRingOrbit

/-! ## Every word of the cap is a base word or a certificate node -/

theorem cover_of_chunk {l : List Nat}
    (h : l.all (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true)
    (X : Nat) (hX : X ∈ l) (hacc : (ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) = true) :
    (fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base ∨ (fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1 := by
  have := List.all_eq_true.1 h X hX
  simp only [hacc, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_0 : (((List.range 2187).drop (250 * 0)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_1 : (((List.range 2187).drop (250 * 1)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_2 : (((List.range 2187).drop (250 * 2)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_3 : (((List.range 2187).drop (250 * 3)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_4 : (((List.range 2187).drop (250 * 4)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_5 : (((List.range 2187).drop (250 * 5)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_6 : (((List.range 2187).drop (250 * 6)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_7 : (((List.range 2187).drop (250 * 7)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_8 : (((List.range 2187).drop (250 * 8)).take 250).all
    (fun X => !(ngon 7).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.base) || decide ((fun i => ⟨wordOf 7 X i, wordOf_ne_zero 7 X i⟩ : Word 7) ∈ Flower7Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

theorem cover : ∀ w ∈ (ngon 7).capWords Ngon.valid7,
    w ∈ Flower7Enum.base ∨ w ∈ Flower7Enum.cert.nodes.map fun t => t.1 := by
  intro w hw
  unfold Pres.capWords at hw
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hw
  obtain ⟨X, ⟨hX, hacc⟩, rfl⟩ := hw
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem (List.mem_range.2 hX) 250 (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [List.length_range] at hlt
  have : j < 9 := by omega
  interval_cases j
  · exact cover_of_chunk cover_chunk_0 X hj hacc
  · exact cover_of_chunk cover_chunk_1 X hj hacc
  · exact cover_of_chunk cover_chunk_2 X hj hacc
  · exact cover_of_chunk cover_chunk_3 X hj hacc
  · exact cover_of_chunk cover_chunk_4 X hj hacc
  · exact cover_of_chunk cover_chunk_5 X hj hacc
  · exact cover_of_chunk cover_chunk_6 X hj hacc
  · exact cover_of_chunk cover_chunk_7 X hj hacc
  · exact cover_of_chunk cover_chunk_8 X hj hacc

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **no least counterexample contains this configuration as a disk** -/
theorem excluded
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (deleted : Finset V)
    (hretainedConnected :
      (G.induce {vertex | deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex | ¬ deletedRegionKeep deleted vertex}).Connected)
    (outerRetained : RetainedDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (outerDeleted : RetainedDart graphData.toRotationSystem (deletedSideKeep deleted))
    (order : Fin 7 ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate 7) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap valid))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b) :
    False :=
  false_of_certificate' graphData minimal deleted hretainedConnected hdeletedConnected
    outerRetained outerDeleted (by norm_num) order hsuccessor K valid iso hports
    (ngon 7) Ngon.valid7 Ngon.disc7 (by norm_num) Flower7Enum.base base_accepts
    Flower7Enum.cert Flower7Enum.ok cover

end Flower7
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
