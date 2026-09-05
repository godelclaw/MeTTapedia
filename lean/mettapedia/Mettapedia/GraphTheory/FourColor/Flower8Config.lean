import Mettapedia.GraphTheory.FourColor.Flower8Base
import Mettapedia.GraphTheory.FourColor.NgonCap

/-! The 8-gon cap's words are covered by the base or the certificate nodes (in chunks of
250 boundary numerals); with the base verification and the cap's disc check,
`false_of_certificate'` excludes the configuration. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace Flower8

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding ZigzagRing TubeRingOrbit

/-! ## Every word of the cap is a base word or a certificate node -/

theorem cover_of_chunk {l : List Nat}
    (h : l.all (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true)
    (X : Nat) (hX : X ∈ l) (hacc : (ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) = true) :
    (fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base ∨ (fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1 := by
  have := List.all_eq_true.1 h X hX
  simp only [hacc, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at this
  exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_0 : (((List.range 6561).drop (250 * 0)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_1 : (((List.range 6561).drop (250 * 1)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_2 : (((List.range 6561).drop (250 * 2)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_3 : (((List.range 6561).drop (250 * 3)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_4 : (((List.range 6561).drop (250 * 4)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_5 : (((List.range 6561).drop (250 * 5)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_6 : (((List.range 6561).drop (250 * 6)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_7 : (((List.range 6561).drop (250 * 7)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_8 : (((List.range 6561).drop (250 * 8)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_9 : (((List.range 6561).drop (250 * 9)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_10 : (((List.range 6561).drop (250 * 10)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_11 : (((List.range 6561).drop (250 * 11)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_12 : (((List.range 6561).drop (250 * 12)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_13 : (((List.range 6561).drop (250 * 13)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_14 : (((List.range 6561).drop (250 * 14)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_15 : (((List.range 6561).drop (250 * 15)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_16 : (((List.range 6561).drop (250 * 16)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_17 : (((List.range 6561).drop (250 * 17)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_18 : (((List.range 6561).drop (250 * 18)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_19 : (((List.range 6561).drop (250 * 19)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_20 : (((List.range 6561).drop (250 * 20)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_21 : (((List.range 6561).drop (250 * 21)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_22 : (((List.range 6561).drop (250 * 22)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_23 : (((List.range 6561).drop (250 * 23)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_24 : (((List.range 6561).drop (250 * 24)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_25 : (((List.range 6561).drop (250 * 25)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cover_chunk_26 : (((List.range 6561).drop (250 * 26)).take 250).all
    (fun X => !(ngon 8).accepts (TubeSlab.Presented.Pres.inWord X) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.base) || decide ((fun i => ⟨wordOf 8 X i, wordOf_ne_zero 8 X i⟩ : Word 8) ∈ Flower8Enum.cert.nodes.map fun t => t.1)) = true := by
  decide +kernel

theorem cover : ∀ w ∈ (ngon 8).capWords Ngon.valid8,
    w ∈ Flower8Enum.base ∨ w ∈ Flower8Enum.cert.nodes.map fun t => t.1 := by
  intro w hw
  unfold Pres.capWords at hw
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hw
  obtain ⟨X, ⟨hX, hacc⟩, rfl⟩ := hw
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem (List.mem_range.2 hX) 250 (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [List.length_range] at hlt
  have : j < 27 := by omega
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
  · exact cover_of_chunk cover_chunk_9 X hj hacc
  · exact cover_of_chunk cover_chunk_10 X hj hacc
  · exact cover_of_chunk cover_chunk_11 X hj hacc
  · exact cover_of_chunk cover_chunk_12 X hj hacc
  · exact cover_of_chunk cover_chunk_13 X hj hacc
  · exact cover_of_chunk cover_chunk_14 X hj hacc
  · exact cover_of_chunk cover_chunk_15 X hj hacc
  · exact cover_of_chunk cover_chunk_16 X hj hacc
  · exact cover_of_chunk cover_chunk_17 X hj hacc
  · exact cover_of_chunk cover_chunk_18 X hj hacc
  · exact cover_of_chunk cover_chunk_19 X hj hacc
  · exact cover_of_chunk cover_chunk_20 X hj hacc
  · exact cover_of_chunk cover_chunk_21 X hj hacc
  · exact cover_of_chunk cover_chunk_22 X hj hacc
  · exact cover_of_chunk cover_chunk_23 X hj hacc
  · exact cover_of_chunk cover_chunk_24 X hj hacc
  · exact cover_of_chunk cover_chunk_25 X hj hacc
  · exact cover_of_chunk cover_chunk_26 X hj hacc

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
    (order : Fin 8 ≃ BoundaryDart graphData.toRotationSystem (deletedRegionKeep deleted))
    (hsuccessor : order.permCongr (finRotate 8) =
      retainedRegionBoundarySuccessor graphData.toRotationSystem (deletedRegionKeep deleted))
    (iso : OpenTangleIso
      (ofVertexSide graphData.toRotationSystem (deletedSideKeep deleted) outerDeleted)
      (K.toCap valid))
    (hports : ∀ b, iso.boundary (complementBoundaryAlphaEquiv graphData.toRotationSystem
      deleted b) = order.symm b) :
    False :=
  false_of_certificate' graphData minimal deleted hretainedConnected hdeletedConnected
    outerRetained outerDeleted (by norm_num) order hsuccessor K valid iso hports
    (ngon 8) Ngon.valid8 Ngon.disc8 (by norm_num) Flower8Enum.base base_accepts
    Flower8Enum.cert Flower8Enum.ok cover

end Flower8
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
