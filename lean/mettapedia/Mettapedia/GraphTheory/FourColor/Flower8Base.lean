import Mettapedia.GraphTheory.FourColor.CapEmbedding
import Mettapedia.GraphTheory.FourColor.NgonCap
import Mettapedia.GraphTheory.FourColor.Flower8Enum

/-!
# The configuration `flower8_tangle.json` is excluded from a least counterexample

The configuration as a presentation (18 vertices, 23 interior edges, ring 8); the
sealed certificate `Flower8Enum` has every base word verified by the enumerator on the
configuration (in chunks of 10), and the 8-gon cap's words are covered by the base or
the certificate nodes (in chunks of 250 boundary numerals).  With the cap's disc check,
`false_of_certificate'` applies.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace PresentedCap
namespace Flower8

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideOpenTangle SimpleGraphDartRotation
open CapEmbedding

/-- the configuration -/
def K : Pres 18 23 8 where
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
    | 5, 2 => Slot.edge 22
    | 6, 0 => Slot.edge 3
    | 6, 1 => Slot.edge 11
    | 6, 2 => Slot.edge 12
    | 7, 0 => Slot.edge 5
    | 7, 1 => Slot.edge 13
    | 7, 2 => Slot.edge 14
    | 8, 0 => Slot.edge 7
    | 8, 1 => Slot.edge 15
    | 8, 2 => Slot.edge 16
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
    | 13, 0 => Slot.edge 16
    | 13, 1 => Slot.edge 17
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
    | 17, 0 => Slot.edge 21
    | 17, 1 => Slot.edge 22
    | 17, 2 => Slot.port 7
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
    | 15, true => (8, 1)
    | 16, false => (8, 2)
    | 16, true => (13, 0)
    | 17, false => (13, 1)
    | 17, true => (14, 0)
    | 18, false => (14, 1)
    | 18, true => (9, 1)
    | 19, false => (9, 2)
    | 19, true => (15, 0)
    | 20, false => (15, 1)
    | 20, true => (16, 0)
    | 21, false => (16, 1)
    | 21, true => (17, 0)
    | 22, false => (17, 1)
    | 22, true => (5, 2)
    | _, _ => (0, 0)
  portPos i := match i with
    | 0 => (10, 2)
    | 1 => (11, 2)
    | 2 => (12, 2)
    | 3 => (13, 2)
    | 4 => (14, 2)
    | 5 => (15, 2)
    | 6 => (16, 2)
    | 7 => (17, 2)
    | _ => (0, 0)

set_option maxRecDepth 100000 in
theorem valid : K.Valid := by decide +kernel

/-! ## Every base word is a support word of the configuration -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_0 : ((Flower8Enum.base.drop (10 * 0)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_1 : ((Flower8Enum.base.drop (10 * 1)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_2 : ((Flower8Enum.base.drop (10 * 2)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_3 : ((Flower8Enum.base.drop (10 * 3)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_4 : ((Flower8Enum.base.drop (10 * 4)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_5 : ((Flower8Enum.base.drop (10 * 5)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_6 : ((Flower8Enum.base.drop (10 * 6)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_7 : ((Flower8Enum.base.drop (10 * 7)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_8 : ((Flower8Enum.base.drop (10 * 8)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_9 : ((Flower8Enum.base.drop (10 * 9)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_10 : ((Flower8Enum.base.drop (10 * 10)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_11 : ((Flower8Enum.base.drop (10 * 11)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_12 : ((Flower8Enum.base.drop (10 * 12)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_13 : ((Flower8Enum.base.drop (10 * 13)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_14 : ((Flower8Enum.base.drop (10 * 14)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_15 : ((Flower8Enum.base.drop (10 * 15)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_16 : ((Flower8Enum.base.drop (10 * 16)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_17 : ((Flower8Enum.base.drop (10 * 17)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_18 : ((Flower8Enum.base.drop (10 * 18)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_19 : ((Flower8Enum.base.drop (10 * 19)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_20 : ((Flower8Enum.base.drop (10 * 20)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_21 : ((Flower8Enum.base.drop (10 * 21)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_22 : ((Flower8Enum.base.drop (10 * 22)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_23 : ((Flower8Enum.base.drop (10 * 23)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_24 : ((Flower8Enum.base.drop (10 * 24)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_25 : ((Flower8Enum.base.drop (10 * 25)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_26 : ((Flower8Enum.base.drop (10 * 26)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_27 : ((Flower8Enum.base.drop (10 * 27)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_28 : ((Flower8Enum.base.drop (10 * 28)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_29 : ((Flower8Enum.base.drop (10 * 29)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_30 : ((Flower8Enum.base.drop (10 * 30)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_31 : ((Flower8Enum.base.drop (10 * 31)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_32 : ((Flower8Enum.base.drop (10 * 32)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_33 : ((Flower8Enum.base.drop (10 * 33)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_34 : ((Flower8Enum.base.drop (10 * 34)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_35 : ((Flower8Enum.base.drop (10 * 35)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_36 : ((Flower8Enum.base.drop (10 * 36)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_37 : ((Flower8Enum.base.drop (10 * 37)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_38 : ((Flower8Enum.base.drop (10 * 38)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_39 : ((Flower8Enum.base.drop (10 * 39)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_40 : ((Flower8Enum.base.drop (10 * 40)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_41 : ((Flower8Enum.base.drop (10 * 41)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_42 : ((Flower8Enum.base.drop (10 * 42)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_43 : ((Flower8Enum.base.drop (10 * 43)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_44 : ((Flower8Enum.base.drop (10 * 44)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_45 : ((Flower8Enum.base.drop (10 * 45)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_46 : ((Flower8Enum.base.drop (10 * 46)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_47 : ((Flower8Enum.base.drop (10 * 47)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_48 : ((Flower8Enum.base.drop (10 * 48)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_49 : ((Flower8Enum.base.drop (10 * 49)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_50 : ((Flower8Enum.base.drop (10 * 50)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_51 : ((Flower8Enum.base.drop (10 * 51)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_52 : ((Flower8Enum.base.drop (10 * 52)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_53 : ((Flower8Enum.base.drop (10 * 53)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_54 : ((Flower8Enum.base.drop (10 * 54)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_55 : ((Flower8Enum.base.drop (10 * 55)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_56 : ((Flower8Enum.base.drop (10 * 56)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_57 : ((Flower8Enum.base.drop (10 * 57)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_58 : ((Flower8Enum.base.drop (10 * 58)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_chunk_59 : ((Flower8Enum.base.drop (10 * 59)).take 10).all (fun u => K.acceptsWord u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem base_length : Flower8Enum.base.length = 600 := by decide +kernel

theorem base_accepts : ∀ u ∈ Flower8Enum.base, K.acceptsWord u = true := by
  intro u hu
  obtain ⟨j, hj⟩ := mem_take_drop_of_mem hu 10 (by norm_num)
  have hlt := lt_of_mem_take_drop hj
  rw [base_length] at hlt
  have : j < 60 := by omega
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
  · exact List.all_eq_true.1 base_chunk_32 u hj
  · exact List.all_eq_true.1 base_chunk_33 u hj
  · exact List.all_eq_true.1 base_chunk_34 u hj
  · exact List.all_eq_true.1 base_chunk_35 u hj
  · exact List.all_eq_true.1 base_chunk_36 u hj
  · exact List.all_eq_true.1 base_chunk_37 u hj
  · exact List.all_eq_true.1 base_chunk_38 u hj
  · exact List.all_eq_true.1 base_chunk_39 u hj
  · exact List.all_eq_true.1 base_chunk_40 u hj
  · exact List.all_eq_true.1 base_chunk_41 u hj
  · exact List.all_eq_true.1 base_chunk_42 u hj
  · exact List.all_eq_true.1 base_chunk_43 u hj
  · exact List.all_eq_true.1 base_chunk_44 u hj
  · exact List.all_eq_true.1 base_chunk_45 u hj
  · exact List.all_eq_true.1 base_chunk_46 u hj
  · exact List.all_eq_true.1 base_chunk_47 u hj
  · exact List.all_eq_true.1 base_chunk_48 u hj
  · exact List.all_eq_true.1 base_chunk_49 u hj
  · exact List.all_eq_true.1 base_chunk_50 u hj
  · exact List.all_eq_true.1 base_chunk_51 u hj
  · exact List.all_eq_true.1 base_chunk_52 u hj
  · exact List.all_eq_true.1 base_chunk_53 u hj
  · exact List.all_eq_true.1 base_chunk_54 u hj
  · exact List.all_eq_true.1 base_chunk_55 u hj
  · exact List.all_eq_true.1 base_chunk_56 u hj
  · exact List.all_eq_true.1 base_chunk_57 u hj
  · exact List.all_eq_true.1 base_chunk_58 u hj
  · exact List.all_eq_true.1 base_chunk_59 u hj

end Flower8
end PresentedCap
end Mettapedia.GraphTheory.FourColor.KempeDerivation
