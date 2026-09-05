import Mettapedia.GraphTheory.FourColor.CapEmbedding
import Mettapedia.GraphTheory.FourColor.NgonCap
import Mettapedia.GraphTheory.FourColor.Flower7Enum

/-!
# The configuration `flower7_tangle.json` is excluded from a least counterexample

The configuration as a presentation (17 vertices, 22 interior edges, ring 7); the
sealed certificate `Flower7Enum` has every base word verified by the enumerator on the
configuration (in chunks of 10), and the 7-gon cap's words are covered by the base or
the certificate nodes (in chunks of 250 boundary numerals).  With the cap's disc check,
`false_of_certificate'` applies.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace Flower7

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding

/-- the configuration -/
def K : Pres 17 22 7 where
  tri v s := match v, s with
    | 0, 0 => Slot.edge 0
    | 0, 1 => Slot.edge 1
    | 0, 2 => Slot.edge 8
    | 1, 0 => Slot.edge 0
    | 1, 1 => Slot.edge 2
    | 1, 2 => Slot.edge 3
    | 2, 0 => Slot.edge 2
    | 2, 1 => Slot.edge 4
    | 2, 2 => Slot.edge 5
    | 3, 0 => Slot.edge 4
    | 3, 1 => Slot.edge 6
    | 3, 2 => Slot.edge 7
    | 4, 0 => Slot.edge 6
    | 4, 1 => Slot.edge 8
    | 4, 2 => Slot.edge 9
    | 5, 0 => Slot.edge 1
    | 5, 1 => Slot.edge 10
    | 5, 2 => Slot.edge 21
    | 6, 0 => Slot.edge 3
    | 6, 1 => Slot.edge 11
    | 6, 2 => Slot.edge 12
    | 7, 0 => Slot.edge 5
    | 7, 1 => Slot.edge 13
    | 7, 2 => Slot.edge 14
    | 8, 0 => Slot.edge 7
    | 8, 1 => Slot.edge 16
    | 8, 2 => Slot.edge 17
    | 9, 0 => Slot.edge 9
    | 9, 1 => Slot.edge 18
    | 9, 2 => Slot.edge 19
    | 10, 0 => Slot.edge 10
    | 10, 1 => Slot.edge 11
    | 10, 2 => Slot.port 0
    | 11, 0 => Slot.edge 12
    | 11, 1 => Slot.edge 13
    | 11, 2 => Slot.port 1
    | 12, 0 => Slot.edge 14
    | 12, 1 => Slot.edge 15
    | 12, 2 => Slot.port 2
    | 13, 0 => Slot.edge 15
    | 13, 1 => Slot.edge 16
    | 13, 2 => Slot.port 3
    | 14, 0 => Slot.edge 17
    | 14, 1 => Slot.edge 18
    | 14, 2 => Slot.port 4
    | 15, 0 => Slot.edge 19
    | 15, 1 => Slot.edge 20
    | 15, 2 => Slot.port 5
    | 16, 0 => Slot.edge 20
    | 16, 1 => Slot.edge 21
    | 16, 2 => Slot.port 6
    | _, _ => Slot.edge 0
  endPos e b := match e, b with
    | 0, false => (0, 0)
    | 0, true => (1, 0)
    | 1, false => (0, 1)
    | 1, true => (5, 0)
    | 2, false => (1, 1)
    | 2, true => (2, 0)
    | 3, false => (1, 2)
    | 3, true => (6, 0)
    | 4, false => (2, 1)
    | 4, true => (3, 0)
    | 5, false => (2, 2)
    | 5, true => (7, 0)
    | 6, false => (3, 1)
    | 6, true => (4, 0)
    | 7, false => (3, 2)
    | 7, true => (8, 0)
    | 8, false => (4, 1)
    | 8, true => (0, 2)
    | 9, false => (4, 2)
    | 9, true => (9, 0)
    | 10, false => (5, 1)
    | 10, true => (10, 0)
    | 11, false => (10, 1)
    | 11, true => (6, 1)
    | 12, false => (6, 2)
    | 12, true => (11, 0)
    | 13, false => (11, 1)
    | 13, true => (7, 1)
    | 14, false => (7, 2)
    | 14, true => (12, 0)
    | 15, false => (12, 1)
    | 15, true => (13, 0)
    | 16, false => (13, 1)
    | 16, true => (8, 1)
    | 17, false => (8, 2)
    | 17, true => (14, 0)
    | 18, false => (14, 1)
    | 18, true => (9, 1)
    | 19, false => (9, 2)
    | 19, true => (15, 0)
    | 20, false => (15, 1)
    | 20, true => (16, 0)
    | 21, false => (16, 1)
    | 21, true => (5, 2)
    | _, _ => (0, 0)
  portPos i := match i with
    | 0 => (10, 2)
    | 1 => (11, 2)
    | 2 => (12, 2)
    | 3 => (13, 2)
    | 4 => (14, 2)
    | 5 => (15, 2)
    | 6 => (16, 2)
    | _ => (0, 0)

set_option maxRecDepth 100000 in
theorem valid : K.Valid := by decide +kernel

/-! ## Every base word is a support word of the configuration -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_0 : ((Flower7Enum.base.drop (10 * 0)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_1 : ((Flower7Enum.base.drop (10 * 1)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_2 : ((Flower7Enum.base.drop (10 * 2)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_3 : ((Flower7Enum.base.drop (10 * 3)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_4 : ((Flower7Enum.base.drop (10 * 4)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_5 : ((Flower7Enum.base.drop (10 * 5)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_6 : ((Flower7Enum.base.drop (10 * 6)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_7 : ((Flower7Enum.base.drop (10 * 7)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_8 : ((Flower7Enum.base.drop (10 * 8)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_9 : ((Flower7Enum.base.drop (10 * 9)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_10 : ((Flower7Enum.base.drop (10 * 10)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_11 : ((Flower7Enum.base.drop (10 * 11)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_12 : ((Flower7Enum.base.drop (10 * 12)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_13 : ((Flower7Enum.base.drop (10 * 13)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_14 : ((Flower7Enum.base.drop (10 * 14)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_15 : ((Flower7Enum.base.drop (10 * 15)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_16 : ((Flower7Enum.base.drop (10 * 16)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_17 : ((Flower7Enum.base.drop (10 * 17)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_18 : ((Flower7Enum.base.drop (10 * 18)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_19 : ((Flower7Enum.base.drop (10 * 19)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_20 : ((Flower7Enum.base.drop (10 * 20)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_21 : ((Flower7Enum.base.drop (10 * 21)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_22 : ((Flower7Enum.base.drop (10 * 22)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_23 : ((Flower7Enum.base.drop (10 * 23)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_24 : ((Flower7Enum.base.drop (10 * 24)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_25 : ((Flower7Enum.base.drop (10 * 25)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_26 : ((Flower7Enum.base.drop (10 * 26)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_27 : ((Flower7Enum.base.drop (10 * 27)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_28 : ((Flower7Enum.base.drop (10 * 28)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_29 : ((Flower7Enum.base.drop (10 * 29)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_30 : ((Flower7Enum.base.drop (10 * 30)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_31 : ((Flower7Enum.base.drop (10 * 31)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem base_length : Flower7Enum.base.length = 312 := by decide +kernel

theorem base_accepts : ∀ u ∈ Flower7Enum.base, K.acceptsWord u = true := by
  intro u hu
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem hu 10 (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [base_length] at hlt
  have : j < 32 := by omega
  interval_cases j
  · exact List.all_eq_true.1 base_chunk_0 u hj
  · exact List.all_eq_true.1 base_chunk_1 u hj
  · exact List.all_eq_true.1 base_chunk_2 u hj
  · exact List.all_eq_true.1 base_chunk_3 u hj
  · exact List.all_eq_true.1 base_chunk_4 u hj
  · exact List.all_eq_true.1 base_chunk_5 u hj
  · exact List.all_eq_true.1 base_chunk_6 u hj
  · exact List.all_eq_true.1 base_chunk_7 u hj
  · exact List.all_eq_true.1 base_chunk_8 u hj
  · exact List.all_eq_true.1 base_chunk_9 u hj
  · exact List.all_eq_true.1 base_chunk_10 u hj
  · exact List.all_eq_true.1 base_chunk_11 u hj
  · exact List.all_eq_true.1 base_chunk_12 u hj
  · exact List.all_eq_true.1 base_chunk_13 u hj
  · exact List.all_eq_true.1 base_chunk_14 u hj
  · exact List.all_eq_true.1 base_chunk_15 u hj
  · exact List.all_eq_true.1 base_chunk_16 u hj
  · exact List.all_eq_true.1 base_chunk_17 u hj
  · exact List.all_eq_true.1 base_chunk_18 u hj
  · exact List.all_eq_true.1 base_chunk_19 u hj
  · exact List.all_eq_true.1 base_chunk_20 u hj
  · exact List.all_eq_true.1 base_chunk_21 u hj
  · exact List.all_eq_true.1 base_chunk_22 u hj
  · exact List.all_eq_true.1 base_chunk_23 u hj
  · exact List.all_eq_true.1 base_chunk_24 u hj
  · exact List.all_eq_true.1 base_chunk_25 u hj
  · exact List.all_eq_true.1 base_chunk_26 u hj
  · exact List.all_eq_true.1 base_chunk_27 u hj
  · exact List.all_eq_true.1 base_chunk_28 u hj
  · exact List.all_eq_true.1 base_chunk_29 u hj
  · exact List.all_eq_true.1 base_chunk_30 u hj
  · exact List.all_eq_true.1 base_chunk_31 u hj

end Flower7
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
