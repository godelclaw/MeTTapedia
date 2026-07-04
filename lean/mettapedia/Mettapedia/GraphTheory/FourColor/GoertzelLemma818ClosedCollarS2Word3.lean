import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarBridgeProof

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word3

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def word : List TauOrient := [TauOrient.mirror, TauOrient.mirror]

def closedStateChunks : List (List (List TauState)) :=
[
  [
    [stateAt 2, stateAt 34]
  , [stateAt 3, stateAt 42]
  , [stateAt 10, stateAt 35]
  , [stateAt 11, stateAt 43]
  , [stateAt 16, stateAt 82]
  , [stateAt 17, stateAt 90]
  , [stateAt 18, stateAt 18]
  , [stateAt 19, stateAt 26]
  , [stateAt 22, stateAt 176]
  , [stateAt 23, stateAt 184]
  , [stateAt 24, stateAt 83]
  , [stateAt 25, stateAt 91]
  , [stateAt 26, stateAt 19]
  , [stateAt 27, stateAt 27]
  , [stateAt 30, stateAt 177]
  , [stateAt 31, stateAt 185]
  , [stateAt 34, stateAt 2]
  , [stateAt 35, stateAt 10]
  , [stateAt 42, stateAt 3]
  , [stateAt 43, stateAt 11]
  , [stateAt 48, stateAt 150]
  , [stateAt 49, stateAt 158]
  , [stateAt 50, stateAt 50]
  , [stateAt 51, stateAt 58]
  , [stateAt 54, stateAt 114]
  , [stateAt 55, stateAt 122]
  , [stateAt 56, stateAt 151]
  , [stateAt 57, stateAt 159]
  , [stateAt 58, stateAt 51]
  , [stateAt 59, stateAt 59]
  , [stateAt 62, stateAt 115]
  , [stateAt 63, stateAt 123]
  ]
, [
    [stateAt 64, stateAt 102]
  , [stateAt 65, stateAt 110]
  , [stateAt 72, stateAt 103]
  , [stateAt 73, stateAt 111]
  , [stateAt 80, stateAt 80]
  , [stateAt 81, stateAt 88]
  , [stateAt 82, stateAt 16]
  , [stateAt 83, stateAt 24]
  , [stateAt 84, stateAt 144]
  , [stateAt 85, stateAt 152]
  , [stateAt 88, stateAt 81]
  , [stateAt 89, stateAt 89]
  , [stateAt 90, stateAt 17]
  , [stateAt 91, stateAt 25]
  , [stateAt 92, stateAt 145]
  , [stateAt 93, stateAt 153]
  , [stateAt 102, stateAt 64]
  , [stateAt 103, stateAt 72]
  , [stateAt 110, stateAt 65]
  , [stateAt 111, stateAt 73]
  , [stateAt 114, stateAt 54]
  , [stateAt 115, stateAt 62]
  , [stateAt 116, stateAt 182]
  , [stateAt 117, stateAt 190]
  , [stateAt 118, stateAt 118]
  , [stateAt 119, stateAt 126]
  , [stateAt 122, stateAt 55]
  , [stateAt 123, stateAt 63]
  , [stateAt 124, stateAt 183]
  , [stateAt 125, stateAt 191]
  , [stateAt 126, stateAt 119]
  , [stateAt 127, stateAt 127]
  ]
, [
    [stateAt 132, stateAt 164]
  , [stateAt 133, stateAt 172]
  , [stateAt 140, stateAt 165]
  , [stateAt 141, stateAt 173]
  , [stateAt 144, stateAt 84]
  , [stateAt 145, stateAt 92]
  , [stateAt 148, stateAt 148]
  , [stateAt 149, stateAt 156]
  , [stateAt 150, stateAt 48]
  , [stateAt 151, stateAt 56]
  , [stateAt 152, stateAt 85]
  , [stateAt 153, stateAt 93]
  , [stateAt 156, stateAt 149]
  , [stateAt 157, stateAt 157]
  , [stateAt 158, stateAt 49]
  , [stateAt 159, stateAt 57]
  , [stateAt 164, stateAt 132]
  , [stateAt 165, stateAt 140]
  , [stateAt 172, stateAt 133]
  , [stateAt 173, stateAt 141]
  , [stateAt 176, stateAt 22]
  , [stateAt 177, stateAt 30]
  , [stateAt 180, stateAt 180]
  , [stateAt 181, stateAt 188]
  , [stateAt 182, stateAt 116]
  , [stateAt 183, stateAt 124]
  , [stateAt 184, stateAt 23]
  , [stateAt 185, stateAt 31]
  , [stateAt 188, stateAt 181]
  , [stateAt 189, stateAt 189]
  , [stateAt 190, stateAt 117]
  , [stateAt 191, stateAt 125]
  ]
]

def closedStates : List (List TauState) :=
  closedStateChunks.flatten

theorem closedStates_chunk0 :
    ((allClosedCollarStates word).drop 0).take 32 =
      listGetD closedStateChunks 0 [] := by
  decide

theorem closedStates_chunk1 :
    ((allClosedCollarStates word).drop 32).take 32 =
      listGetD closedStateChunks 1 [] := by
  decide

theorem closedStates_chunk2 :
    ((allClosedCollarStates word).drop 64).take 32 =
      listGetD closedStateChunks 2 [] := by
  decide

theorem closedStates_chunks_terminal :
    (allClosedCollarStates word).drop (closedStateChunks.length * 32) = [] := by
  decide

theorem closedStates_chunks_get
    (i : Nat) (hi : i < closedStateChunks.length) :
    ((allClosedCollarStates word).drop (i * 32)).take 32 =
      listGetD closedStateChunks i [] := by
  have hlen : closedStateChunks.length = 3 := by
    rfl
  by_cases h0 : i = 0
  · subst i
    simpa using closedStates_chunk0
  by_cases h1 : i = 1
  · subst i
    simpa using closedStates_chunk1
  by_cases h2 : i = 2
  · subst i
    simpa using closedStates_chunk2
  · have hbound : i < 3 := by
      simpa [hlen] using hi
    omega

theorem closedStates_eq : allClosedCollarStates word = closedStates := by
  have h := list_eq_join_chunks_of_drop_take
    (allClosedCollarStates word) 32 closedStateChunks
    closedStates_chunks_get closedStates_chunks_terminal
  simpa [closedStates] using h

theorem cert0_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.r, LColor.r] = [] := by
  decide

theorem cert0_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert0_empty

theorem cert1_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.r, LColor.b] = [] := by
  decide

theorem cert1_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert1_empty

theorem cert2_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.r, LColor.p] = [] := by
  decide

theorem cert2_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert2_empty

def fiber3 : List (List TauState) :=
[
  [stateAt 122, stateAt 55]
, [stateAt 123, stateAt 63]
]

theorem fiber3_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.b, LColor.r] = fiber3 := by
  decide

def cert3 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.b, LColor.r],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert3_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert3_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert3_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert3_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert3_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber3 0 [])
      LColor.r LColor.b cert3_seen_0_1_0 = cert3_layer_0_1_0 := by
  decide

def cert3_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert3_layer_0_1_1 : List ChainEdge :=
  []

theorem cert3_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber3 0 [])
      LColor.r LColor.b cert3_seen_0_1_1 = cert3_layer_0_1_1 := by
  decide

theorem cert3_component_0_1_eq :
    closedCollarComponent word (listGetD fiber3 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert3_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber3 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber3 0 [])
      LColor.r LColor.b 18 cert3_seen_0_1_0 = cert3_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber3 0 []) LColor.r LColor.b
    cert3_seen_0_1_0 cert3_layer_0_1_0 17 cert3_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber3 0 [])
      LColor.r LColor.b 17 cert3_seen_0_1_1 = cert3_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber3 0 []) LColor.r LColor.b
    cert3_seen_0_1_1 cert3_layer_0_1_1_eq 17

theorem cert3_step_0_1 :
    closedCollarIndexStepBool word fiber3 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert3_move_0_1)
    (by decide) (by decide)
    (by simpa [cert3_move_0_1] using cert3_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert3_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert3_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert3_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert3_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert3_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber3 1 [])
      LColor.r LColor.b cert3_seen_1_0_0 = cert3_layer_1_0_0 := by
  decide

def cert3_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert3_layer_1_0_1 : List ChainEdge :=
  []

theorem cert3_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber3 1 [])
      LColor.r LColor.b cert3_seen_1_0_1 = cert3_layer_1_0_1 := by
  decide

theorem cert3_component_1_0_eq :
    closedCollarComponent word (listGetD fiber3 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert3_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber3 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber3 1 [])
      LColor.r LColor.b 18 cert3_seen_1_0_0 = cert3_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber3 1 []) LColor.r LColor.b
    cert3_seen_1_0_0 cert3_layer_1_0_0 17 cert3_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber3 1 [])
      LColor.r LColor.b 17 cert3_seen_1_0_1 = cert3_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber3 1 []) LColor.r LColor.b
    cert3_seen_1_0_1 cert3_layer_1_0_1_eq 17

theorem cert3_step_1_0 :
    closedCollarIndexStepBool word fiber3 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert3_move_1_0)
    (by decide) (by decide)
    (by simpa [cert3_move_1_0] using cert3_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert3_row_0 :
    closedCollarParentIndexValid word fiber3 cert3.parents 0 = true := by
  have cert3_fiber_length : fiber3.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert3, listGetD, cert3_fiber_length]

theorem cert3_row_1 :
    closedCollarParentIndexValid word fiber3 cert3.parents 1 = true := by
  have cert3_fiber_length : fiber3.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert3, listGetD, cert3_fiber_length, cert3_step_1_0, cert3_step_0_1]

theorem cert3_rows :
    closedCollarSpineRowsValid word fiber3 cert3.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert3_fiber_length : fiber3.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert3_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert3_row_1
  · omega

theorem cert3_root :
    closedCollarSpineParentsReachRoot fiber3 cert3 = true := by
  decide

theorem cert3_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.b, LColor.r] := by
  change closedCollarFiberKempeConnected word cert3.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert3 closedStates_eq fiber3_eq cert3_rows cert3_root

def fiber4 : List (List TauState) :=
[
  [stateAt 10, stateAt 35]
, [stateAt 11, stateAt 43]
, [stateAt 56, stateAt 151]
, [stateAt 57, stateAt 159]
, [stateAt 58, stateAt 51]
, [stateAt 59, stateAt 59]
]

theorem fiber4_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.b, LColor.b] = fiber4 := by
  decide

def cert4 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.b, LColor.b],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 5, 4, 0, 1] }

def cert4_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert4_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert4_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert4_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.r LColor.p cert4_seen_0_1_0 = cert4_layer_0_1_0 := by
  decide

def cert4_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_layer_0_1_1 : List ChainEdge :=
  []

theorem cert4_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.r LColor.p cert4_seen_0_1_1 = cert4_layer_0_1_1 := by
  decide

theorem cert4_component_0_1_eq :
    closedCollarComponent word (listGetD fiber4 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert4_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.r LColor.p 18 cert4_seen_0_1_0 = cert4_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 0 []) LColor.r LColor.p
    cert4_seen_0_1_0 cert4_layer_0_1_0 17 cert4_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.r LColor.p 17 cert4_seen_0_1_1 = cert4_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 0 []) LColor.r LColor.p
    cert4_seen_0_1_1 cert4_layer_0_1_1_eq 17

theorem cert4_step_0_1 :
    closedCollarIndexStepBool word fiber4 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_0_1)
    (by decide) (by decide)
    (by simpa [cert4_move_0_1] using cert4_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert4_move_0_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert4_component_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert4_seen_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert4_layer_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert4_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.b LColor.p cert4_seen_0_4_0 = cert4_layer_0_4_0 := by
  decide

def cert4_seen_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert4_layer_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert4_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.b LColor.p cert4_seen_0_4_1 = cert4_layer_0_4_1 := by
  decide

def cert4_seen_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert4_layer_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert4_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.b LColor.p cert4_seen_0_4_2 = cert4_layer_0_4_2 := by
  decide

def cert4_seen_0_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert4_layer_0_4_3 : List ChainEdge :=
  []

theorem cert4_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 0 [])
      LColor.b LColor.p cert4_seen_0_4_3 = cert4_layer_0_4_3 := by
  decide

theorem cert4_component_0_4_eq :
    closedCollarComponent word (listGetD fiber4 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert4_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.b LColor.p 18 cert4_seen_0_4_0 = cert4_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 0 []) LColor.b LColor.p
    cert4_seen_0_4_0 cert4_layer_0_4_0 17 cert4_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.b LColor.p 17 cert4_seen_0_4_1 = cert4_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 0 []) LColor.b LColor.p
    cert4_seen_0_4_1 cert4_layer_0_4_1 16 cert4_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.b LColor.p 16 cert4_seen_0_4_2 = cert4_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 0 []) LColor.b LColor.p
    cert4_seen_0_4_2 cert4_layer_0_4_2 15 cert4_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 0 [])
      LColor.b LColor.p 15 cert4_seen_0_4_3 = cert4_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 0 []) LColor.b LColor.p
    cert4_seen_0_4_3 cert4_layer_0_4_3_eq 15

theorem cert4_step_0_4 :
    closedCollarIndexStepBool word fiber4 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_0_4)
    (by decide) (by decide)
    (by simpa [cert4_move_0_4] using cert4_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert4_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert4_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert4_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert4_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.r LColor.p cert4_seen_1_0_0 = cert4_layer_1_0_0 := by
  decide

def cert4_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_layer_1_0_1 : List ChainEdge :=
  []

theorem cert4_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.r LColor.p cert4_seen_1_0_1 = cert4_layer_1_0_1 := by
  decide

theorem cert4_component_1_0_eq :
    closedCollarComponent word (listGetD fiber4 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert4_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.r LColor.p 18 cert4_seen_1_0_0 = cert4_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 1 []) LColor.r LColor.p
    cert4_seen_1_0_0 cert4_layer_1_0_0 17 cert4_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.r LColor.p 17 cert4_seen_1_0_1 = cert4_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 1 []) LColor.r LColor.p
    cert4_seen_1_0_1 cert4_layer_1_0_1_eq 17

theorem cert4_step_1_0 :
    closedCollarIndexStepBool word fiber4 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_1_0)
    (by decide) (by decide)
    (by simpa [cert4_move_1_0] using cert4_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert4_move_1_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert4_component_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_seen_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert4_layer_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert4_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.b LColor.p cert4_seen_1_5_0 = cert4_layer_1_5_0 := by
  decide

def cert4_seen_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert4_layer_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert4_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.b LColor.p cert4_seen_1_5_1 = cert4_layer_1_5_1 := by
  decide

def cert4_seen_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert4_layer_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert4_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.b LColor.p cert4_seen_1_5_2 = cert4_layer_1_5_2 := by
  decide

def cert4_seen_1_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_layer_1_5_3 : List ChainEdge :=
  []

theorem cert4_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 1 [])
      LColor.b LColor.p cert4_seen_1_5_3 = cert4_layer_1_5_3 := by
  decide

theorem cert4_component_1_5_eq :
    closedCollarComponent word (listGetD fiber4 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert4_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.b LColor.p 18 cert4_seen_1_5_0 = cert4_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 1 []) LColor.b LColor.p
    cert4_seen_1_5_0 cert4_layer_1_5_0 17 cert4_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.b LColor.p 17 cert4_seen_1_5_1 = cert4_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 1 []) LColor.b LColor.p
    cert4_seen_1_5_1 cert4_layer_1_5_1 16 cert4_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.b LColor.p 16 cert4_seen_1_5_2 = cert4_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 1 []) LColor.b LColor.p
    cert4_seen_1_5_2 cert4_layer_1_5_2 15 cert4_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 1 [])
      LColor.b LColor.p 15 cert4_seen_1_5_3 = cert4_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 1 []) LColor.b LColor.p
    cert4_seen_1_5_3 cert4_layer_1_5_3_eq 15

theorem cert4_step_1_5 :
    closedCollarIndexStepBool word fiber4 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_1_5)
    (by decide) (by decide)
    (by simpa [cert4_move_1_5] using cert4_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert4_move_2_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert4_component_2_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_seen_2_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert4_layer_2_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert4_layer_2_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 2 [])
      LColor.r LColor.p cert4_seen_2_5_0 = cert4_layer_2_5_0 := by
  decide

def cert4_seen_2_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert4_layer_2_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert4_layer_2_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 2 [])
      LColor.r LColor.p cert4_seen_2_5_1 = cert4_layer_2_5_1 := by
  decide

def cert4_seen_2_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert4_layer_2_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert4_layer_2_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 2 [])
      LColor.r LColor.p cert4_seen_2_5_2 = cert4_layer_2_5_2 := by
  decide

def cert4_seen_2_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_layer_2_5_3 : List ChainEdge :=
  []

theorem cert4_layer_2_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 2 [])
      LColor.r LColor.p cert4_seen_2_5_3 = cert4_layer_2_5_3 := by
  decide

theorem cert4_component_2_5_eq :
    closedCollarComponent word (listGetD fiber4 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert4_component_2_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 2 [])
      LColor.r LColor.p 18 cert4_seen_2_5_0 = cert4_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 2 []) LColor.r LColor.p
    cert4_seen_2_5_0 cert4_layer_2_5_0 17 cert4_layer_2_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 2 [])
      LColor.r LColor.p 17 cert4_seen_2_5_1 = cert4_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 2 []) LColor.r LColor.p
    cert4_seen_2_5_1 cert4_layer_2_5_1 16 cert4_layer_2_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 2 [])
      LColor.r LColor.p 16 cert4_seen_2_5_2 = cert4_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 2 []) LColor.r LColor.p
    cert4_seen_2_5_2 cert4_layer_2_5_2 15 cert4_layer_2_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 2 [])
      LColor.r LColor.p 15 cert4_seen_2_5_3 = cert4_component_2_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 2 []) LColor.r LColor.p
    cert4_seen_2_5_3 cert4_layer_2_5_3_eq 15

theorem cert4_step_2_5 :
    closedCollarIndexStepBool word fiber4 2 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_2_5)
    (by decide) (by decide)
    (by simpa [cert4_move_2_5] using cert4_component_2_5_eq)
    (by decide) (by decide) (by decide)

def cert4_move_3_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert4_component_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_seen_3_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert4_layer_3_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert4_layer_3_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 3 [])
      LColor.r LColor.p cert4_seen_3_4_0 = cert4_layer_3_4_0 := by
  decide

def cert4_seen_3_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert4_layer_3_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert4_layer_3_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 3 [])
      LColor.r LColor.p cert4_seen_3_4_1 = cert4_layer_3_4_1 := by
  decide

def cert4_seen_3_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert4_layer_3_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert4_layer_3_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 3 [])
      LColor.r LColor.p cert4_seen_3_4_2 = cert4_layer_3_4_2 := by
  decide

def cert4_seen_3_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_layer_3_4_3 : List ChainEdge :=
  []

theorem cert4_layer_3_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 3 [])
      LColor.r LColor.p cert4_seen_3_4_3 = cert4_layer_3_4_3 := by
  decide

theorem cert4_component_3_4_eq :
    closedCollarComponent word (listGetD fiber4 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert4_component_3_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 3 [])
      LColor.r LColor.p 18 cert4_seen_3_4_0 = cert4_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 3 []) LColor.r LColor.p
    cert4_seen_3_4_0 cert4_layer_3_4_0 17 cert4_layer_3_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 3 [])
      LColor.r LColor.p 17 cert4_seen_3_4_1 = cert4_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 3 []) LColor.r LColor.p
    cert4_seen_3_4_1 cert4_layer_3_4_1 16 cert4_layer_3_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 3 [])
      LColor.r LColor.p 16 cert4_seen_3_4_2 = cert4_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 3 []) LColor.r LColor.p
    cert4_seen_3_4_2 cert4_layer_3_4_2 15 cert4_layer_3_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 3 [])
      LColor.r LColor.p 15 cert4_seen_3_4_3 = cert4_component_3_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 3 []) LColor.r LColor.p
    cert4_seen_3_4_3 cert4_layer_3_4_3_eq 15

theorem cert4_step_3_4 :
    closedCollarIndexStepBool word fiber4 3 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_3_4)
    (by decide) (by decide)
    (by simpa [cert4_move_3_4] using cert4_component_3_4_eq)
    (by decide) (by decide) (by decide)

def cert4_move_4_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert4_component_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert4_seen_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert4_layer_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert4_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.b LColor.p cert4_seen_4_0_0 = cert4_layer_4_0_0 := by
  decide

def cert4_seen_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert4_layer_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert4_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.b LColor.p cert4_seen_4_0_1 = cert4_layer_4_0_1 := by
  decide

def cert4_seen_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert4_layer_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert4_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.b LColor.p cert4_seen_4_0_2 = cert4_layer_4_0_2 := by
  decide

def cert4_seen_4_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert4_layer_4_0_3 : List ChainEdge :=
  []

theorem cert4_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.b LColor.p cert4_seen_4_0_3 = cert4_layer_4_0_3 := by
  decide

theorem cert4_component_4_0_eq :
    closedCollarComponent word (listGetD fiber4 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert4_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.b LColor.p 18 cert4_seen_4_0_0 = cert4_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.b LColor.p
    cert4_seen_4_0_0 cert4_layer_4_0_0 17 cert4_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.b LColor.p 17 cert4_seen_4_0_1 = cert4_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.b LColor.p
    cert4_seen_4_0_1 cert4_layer_4_0_1 16 cert4_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.b LColor.p 16 cert4_seen_4_0_2 = cert4_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.b LColor.p
    cert4_seen_4_0_2 cert4_layer_4_0_2 15 cert4_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.b LColor.p 15 cert4_seen_4_0_3 = cert4_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 4 []) LColor.b LColor.p
    cert4_seen_4_0_3 cert4_layer_4_0_3_eq 15

theorem cert4_step_4_0 :
    closedCollarIndexStepBool word fiber4 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_4_0)
    (by decide) (by decide)
    (by simpa [cert4_move_4_0] using cert4_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert4_move_4_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert4_component_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_seen_4_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert4_layer_4_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert4_layer_4_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.r LColor.p cert4_seen_4_3_0 = cert4_layer_4_3_0 := by
  decide

def cert4_seen_4_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert4_layer_4_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert4_layer_4_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.r LColor.p cert4_seen_4_3_1 = cert4_layer_4_3_1 := by
  decide

def cert4_seen_4_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert4_layer_4_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert4_layer_4_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.r LColor.p cert4_seen_4_3_2 = cert4_layer_4_3_2 := by
  decide

def cert4_seen_4_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_layer_4_3_3 : List ChainEdge :=
  []

theorem cert4_layer_4_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 4 [])
      LColor.r LColor.p cert4_seen_4_3_3 = cert4_layer_4_3_3 := by
  decide

theorem cert4_component_4_3_eq :
    closedCollarComponent word (listGetD fiber4 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert4_component_4_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.r LColor.p 18 cert4_seen_4_3_0 = cert4_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.r LColor.p
    cert4_seen_4_3_0 cert4_layer_4_3_0 17 cert4_layer_4_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.r LColor.p 17 cert4_seen_4_3_1 = cert4_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.r LColor.p
    cert4_seen_4_3_1 cert4_layer_4_3_1 16 cert4_layer_4_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.r LColor.p 16 cert4_seen_4_3_2 = cert4_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 4 []) LColor.r LColor.p
    cert4_seen_4_3_2 cert4_layer_4_3_2 15 cert4_layer_4_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 4 [])
      LColor.r LColor.p 15 cert4_seen_4_3_3 = cert4_component_4_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 4 []) LColor.r LColor.p
    cert4_seen_4_3_3 cert4_layer_4_3_3_eq 15

theorem cert4_step_4_3 :
    closedCollarIndexStepBool word fiber4 4 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_4_3)
    (by decide) (by decide)
    (by simpa [cert4_move_4_3] using cert4_component_4_3_eq)
    (by decide) (by decide) (by decide)

def cert4_move_5_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert4_component_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_seen_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert4_layer_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert4_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.b LColor.p cert4_seen_5_1_0 = cert4_layer_5_1_0 := by
  decide

def cert4_seen_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert4_layer_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert4_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.b LColor.p cert4_seen_5_1_1 = cert4_layer_5_1_1 := by
  decide

def cert4_seen_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert4_layer_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert4_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.b LColor.p cert4_seen_5_1_2 = cert4_layer_5_1_2 := by
  decide

def cert4_seen_5_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert4_layer_5_1_3 : List ChainEdge :=
  []

theorem cert4_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.b LColor.p cert4_seen_5_1_3 = cert4_layer_5_1_3 := by
  decide

theorem cert4_component_5_1_eq :
    closedCollarComponent word (listGetD fiber4 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert4_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.b LColor.p 18 cert4_seen_5_1_0 = cert4_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.b LColor.p
    cert4_seen_5_1_0 cert4_layer_5_1_0 17 cert4_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.b LColor.p 17 cert4_seen_5_1_1 = cert4_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.b LColor.p
    cert4_seen_5_1_1 cert4_layer_5_1_1 16 cert4_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.b LColor.p 16 cert4_seen_5_1_2 = cert4_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.b LColor.p
    cert4_seen_5_1_2 cert4_layer_5_1_2 15 cert4_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.b LColor.p 15 cert4_seen_5_1_3 = cert4_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 5 []) LColor.b LColor.p
    cert4_seen_5_1_3 cert4_layer_5_1_3_eq 15

theorem cert4_step_5_1 :
    closedCollarIndexStepBool word fiber4 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_5_1)
    (by decide) (by decide)
    (by simpa [cert4_move_5_1] using cert4_component_5_1_eq)
    (by decide) (by decide) (by decide)

def cert4_move_5_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert4_component_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_seen_5_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert4_layer_5_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert4_layer_5_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.r LColor.p cert4_seen_5_2_0 = cert4_layer_5_2_0 := by
  decide

def cert4_seen_5_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert4_layer_5_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert4_layer_5_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.r LColor.p cert4_seen_5_2_1 = cert4_layer_5_2_1 := by
  decide

def cert4_seen_5_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert4_layer_5_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert4_layer_5_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.r LColor.p cert4_seen_5_2_2 = cert4_layer_5_2_2 := by
  decide

def cert4_seen_5_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert4_layer_5_2_3 : List ChainEdge :=
  []

theorem cert4_layer_5_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber4 5 [])
      LColor.r LColor.p cert4_seen_5_2_3 = cert4_layer_5_2_3 := by
  decide

theorem cert4_component_5_2_eq :
    closedCollarComponent word (listGetD fiber4 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert4_component_5_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber4 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.r LColor.p 18 cert4_seen_5_2_0 = cert4_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.r LColor.p
    cert4_seen_5_2_0 cert4_layer_5_2_0 17 cert4_layer_5_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.r LColor.p 17 cert4_seen_5_2_1 = cert4_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.r LColor.p
    cert4_seen_5_2_1 cert4_layer_5_2_1 16 cert4_layer_5_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.r LColor.p 16 cert4_seen_5_2_2 = cert4_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber4 5 []) LColor.r LColor.p
    cert4_seen_5_2_2 cert4_layer_5_2_2 15 cert4_layer_5_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber4 5 [])
      LColor.r LColor.p 15 cert4_seen_5_2_3 = cert4_component_5_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber4 5 []) LColor.r LColor.p
    cert4_seen_5_2_3 cert4_layer_5_2_3_eq 15

theorem cert4_step_5_2 :
    closedCollarIndexStepBool word fiber4 5 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert4_move_5_2)
    (by decide) (by decide)
    (by simpa [cert4_move_5_2] using cert4_component_5_2_eq)
    (by decide) (by decide) (by decide)

theorem cert4_row_0 :
    closedCollarParentIndexValid word fiber4 cert4.parents 0 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length]

theorem cert4_row_1 :
    closedCollarParentIndexValid word fiber4 cert4.parents 1 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length, cert4_step_1_0, cert4_step_0_1]

theorem cert4_row_2 :
    closedCollarParentIndexValid word fiber4 cert4.parents 2 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length, cert4_step_2_5, cert4_step_5_2]

theorem cert4_row_3 :
    closedCollarParentIndexValid word fiber4 cert4.parents 3 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length, cert4_step_3_4, cert4_step_4_3]

theorem cert4_row_4 :
    closedCollarParentIndexValid word fiber4 cert4.parents 4 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length, cert4_step_4_0, cert4_step_0_4]

theorem cert4_row_5 :
    closedCollarParentIndexValid word fiber4 cert4.parents 5 = true := by
  have cert4_fiber_length : fiber4.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert4, listGetD, cert4_fiber_length, cert4_step_5_1, cert4_step_1_5]

theorem cert4_rows :
    closedCollarSpineRowsValid word fiber4 cert4.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert4_fiber_length : fiber4.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert4_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert4_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert4_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert4_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert4_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert4_row_5
  · omega

theorem cert4_root :
    closedCollarSpineParentsReachRoot fiber4 cert4 = true := by
  decide

theorem cert4_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.b, LColor.b] := by
  change closedCollarFiberKempeConnected word cert4.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert4 closedStates_eq fiber4_eq cert4_rows cert4_root

theorem cert5_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.b, LColor.p] = [] := by
  decide

theorem cert5_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert5_empty

def fiber6 : List (List TauState) :=
[
  [stateAt 184, stateAt 23]
, [stateAt 185, stateAt 31]
]

theorem fiber6_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.p, LColor.r] = fiber6 := by
  decide

def cert6 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.p, LColor.r],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert6_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert6_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert6_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert6_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert6_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber6 0 [])
      LColor.r LColor.p cert6_seen_0_1_0 = cert6_layer_0_1_0 := by
  decide

def cert6_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert6_layer_0_1_1 : List ChainEdge :=
  []

theorem cert6_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber6 0 [])
      LColor.r LColor.p cert6_seen_0_1_1 = cert6_layer_0_1_1 := by
  decide

theorem cert6_component_0_1_eq :
    closedCollarComponent word (listGetD fiber6 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert6_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber6 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber6 0 [])
      LColor.r LColor.p 18 cert6_seen_0_1_0 = cert6_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber6 0 []) LColor.r LColor.p
    cert6_seen_0_1_0 cert6_layer_0_1_0 17 cert6_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber6 0 [])
      LColor.r LColor.p 17 cert6_seen_0_1_1 = cert6_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber6 0 []) LColor.r LColor.p
    cert6_seen_0_1_1 cert6_layer_0_1_1_eq 17

theorem cert6_step_0_1 :
    closedCollarIndexStepBool word fiber6 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert6_move_0_1)
    (by decide) (by decide)
    (by simpa [cert6_move_0_1] using cert6_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert6_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert6_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert6_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert6_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert6_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber6 1 [])
      LColor.r LColor.p cert6_seen_1_0_0 = cert6_layer_1_0_0 := by
  decide

def cert6_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert6_layer_1_0_1 : List ChainEdge :=
  []

theorem cert6_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber6 1 [])
      LColor.r LColor.p cert6_seen_1_0_1 = cert6_layer_1_0_1 := by
  decide

theorem cert6_component_1_0_eq :
    closedCollarComponent word (listGetD fiber6 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert6_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber6 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber6 1 [])
      LColor.r LColor.p 18 cert6_seen_1_0_0 = cert6_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber6 1 []) LColor.r LColor.p
    cert6_seen_1_0_0 cert6_layer_1_0_0 17 cert6_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber6 1 [])
      LColor.r LColor.p 17 cert6_seen_1_0_1 = cert6_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber6 1 []) LColor.r LColor.p
    cert6_seen_1_0_1 cert6_layer_1_0_1_eq 17

theorem cert6_step_1_0 :
    closedCollarIndexStepBool word fiber6 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert6_move_1_0)
    (by decide) (by decide)
    (by simpa [cert6_move_1_0] using cert6_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert6_row_0 :
    closedCollarParentIndexValid word fiber6 cert6.parents 0 = true := by
  have cert6_fiber_length : fiber6.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert6, listGetD, cert6_fiber_length]

theorem cert6_row_1 :
    closedCollarParentIndexValid word fiber6 cert6.parents 1 = true := by
  have cert6_fiber_length : fiber6.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert6, listGetD, cert6_fiber_length, cert6_step_1_0, cert6_step_0_1]

theorem cert6_rows :
    closedCollarSpineRowsValid word fiber6 cert6.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert6_fiber_length : fiber6.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert6_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert6_row_1
  · omega

theorem cert6_root :
    closedCollarSpineParentsReachRoot fiber6 cert6 = true := by
  decide

theorem cert6_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.r] := by
  change closedCollarFiberKempeConnected word cert6.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert6 closedStates_eq fiber6_eq cert6_rows cert6_root

theorem cert7_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.p, LColor.b] = [] := by
  decide

theorem cert7_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert7_empty

def fiber8 : List (List TauState) :=
[
  [stateAt 24, stateAt 83]
, [stateAt 25, stateAt 91]
, [stateAt 26, stateAt 19]
, [stateAt 27, stateAt 27]
, [stateAt 42, stateAt 3]
, [stateAt 43, stateAt 11]
]

theorem fiber8_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.r, LColor.p, LColor.p] = fiber8 := by
  decide

def cert8 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.p, LColor.p],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 0, 1, 2, 3] }

def cert8_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_0 = cert8_layer_0_1_0 := by
  decide

def cert8_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_0_1_1 : List ChainEdge :=
  []

theorem cert8_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_1 = cert8_layer_0_1_1 := by
  decide

theorem cert8_component_0_1_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 18 cert8_seen_0_1_0 = cert8_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_1_0 cert8_layer_0_1_0 17 cert8_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 17 cert8_seen_0_1_1 = cert8_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_1_1 cert8_layer_0_1_1_eq 17

theorem cert8_step_0_1 :
    closedCollarIndexStepBool word fiber8 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_1)
    (by decide) (by decide)
    (by simpa [cert8_move_0_1] using cert8_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_0 = cert8_layer_0_2_0 := by
  decide

def cert8_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_1 = cert8_layer_0_2_1 := by
  decide

def cert8_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_2 = cert8_layer_0_2_2 := by
  decide

def cert8_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_0_2_3 : List ChainEdge :=
  []

theorem cert8_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_3 = cert8_layer_0_2_3 := by
  decide

theorem cert8_component_0_2_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 18 cert8_seen_0_2_0 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_0 cert8_layer_0_2_0 17 cert8_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 17 cert8_seen_0_2_1 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_1 cert8_layer_0_2_1 16 cert8_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 16 cert8_seen_0_2_2 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_2 cert8_layer_0_2_2 15 cert8_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 15 cert8_seen_0_2_3 = cert8_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_3 cert8_layer_0_2_3_eq 15

theorem cert8_step_0_2 :
    closedCollarIndexStepBool word fiber8 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_2)
    (by decide) (by decide)
    (by simpa [cert8_move_0_2] using cert8_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_0 = cert8_layer_1_0_0 := by
  decide

def cert8_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_1_0_1 : List ChainEdge :=
  []

theorem cert8_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_1 = cert8_layer_1_0_1 := by
  decide

theorem cert8_component_1_0_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 18 cert8_seen_1_0_0 = cert8_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_0_0 cert8_layer_1_0_0 17 cert8_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 17 cert8_seen_1_0_1 = cert8_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_0_1 cert8_layer_1_0_1_eq 17

theorem cert8_step_1_0 :
    closedCollarIndexStepBool word fiber8 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_0)
    (by decide) (by decide)
    (by simpa [cert8_move_1_0] using cert8_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_0 = cert8_layer_1_3_0 := by
  decide

def cert8_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_1 = cert8_layer_1_3_1 := by
  decide

def cert8_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_2 = cert8_layer_1_3_2 := by
  decide

def cert8_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_1_3_3 : List ChainEdge :=
  []

theorem cert8_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_3 = cert8_layer_1_3_3 := by
  decide

theorem cert8_component_1_3_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 18 cert8_seen_1_3_0 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_0 cert8_layer_1_3_0 17 cert8_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 17 cert8_seen_1_3_1 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_1 cert8_layer_1_3_1 16 cert8_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 16 cert8_seen_1_3_2 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_2 cert8_layer_1_3_2 15 cert8_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 15 cert8_seen_1_3_3 = cert8_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_3 cert8_layer_1_3_3_eq 15

theorem cert8_step_1_3 :
    closedCollarIndexStepBool word fiber8 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_3)
    (by decide) (by decide)
    (by simpa [cert8_move_1_3] using cert8_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_0 = cert8_layer_2_0_0 := by
  decide

def cert8_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_1 = cert8_layer_2_0_1 := by
  decide

def cert8_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_2 = cert8_layer_2_0_2 := by
  decide

def cert8_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_2_0_3 : List ChainEdge :=
  []

theorem cert8_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_3 = cert8_layer_2_0_3 := by
  decide

theorem cert8_component_2_0_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 18 cert8_seen_2_0_0 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_0 cert8_layer_2_0_0 17 cert8_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 17 cert8_seen_2_0_1 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_1 cert8_layer_2_0_1 16 cert8_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 16 cert8_seen_2_0_2 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_2 cert8_layer_2_0_2 15 cert8_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 15 cert8_seen_2_0_3 = cert8_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_3 cert8_layer_2_0_3_eq 15

theorem cert8_step_2_0 :
    closedCollarIndexStepBool word fiber8 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_0)
    (by decide) (by decide)
    (by simpa [cert8_move_2_0] using cert8_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_4_0 = cert8_layer_2_4_0 := by
  decide

def cert8_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_4_1 = cert8_layer_2_4_1 := by
  decide

def cert8_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_4_2 = cert8_layer_2_4_2 := by
  decide

def cert8_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_2_4_3 : List ChainEdge :=
  []

theorem cert8_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_4_3 = cert8_layer_2_4_3 := by
  decide

theorem cert8_component_2_4_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 18 cert8_seen_2_4_0 = cert8_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_4_0 cert8_layer_2_4_0 17 cert8_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 17 cert8_seen_2_4_1 = cert8_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_4_1 cert8_layer_2_4_1 16 cert8_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 16 cert8_seen_2_4_2 = cert8_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_4_2 cert8_layer_2_4_2 15 cert8_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 15 cert8_seen_2_4_3 = cert8_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_4_3 cert8_layer_2_4_3_eq 15

theorem cert8_step_2_4 :
    closedCollarIndexStepBool word fiber8 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_4)
    (by decide) (by decide)
    (by simpa [cert8_move_2_4] using cert8_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_0 = cert8_layer_3_1_0 := by
  decide

def cert8_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_1 = cert8_layer_3_1_1 := by
  decide

def cert8_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_2 = cert8_layer_3_1_2 := by
  decide

def cert8_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_3_1_3 : List ChainEdge :=
  []

theorem cert8_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_3 = cert8_layer_3_1_3 := by
  decide

theorem cert8_component_3_1_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 18 cert8_seen_3_1_0 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_0 cert8_layer_3_1_0 17 cert8_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 17 cert8_seen_3_1_1 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_1 cert8_layer_3_1_1 16 cert8_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 16 cert8_seen_3_1_2 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_2 cert8_layer_3_1_2 15 cert8_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 15 cert8_seen_3_1_3 = cert8_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_3 cert8_layer_3_1_3_eq 15

theorem cert8_step_3_1 :
    closedCollarIndexStepBool word fiber8 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_1)
    (by decide) (by decide)
    (by simpa [cert8_move_3_1] using cert8_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_5_0 = cert8_layer_3_5_0 := by
  decide

def cert8_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_5_1 = cert8_layer_3_5_1 := by
  decide

def cert8_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_5_2 = cert8_layer_3_5_2 := by
  decide

def cert8_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_3_5_3 : List ChainEdge :=
  []

theorem cert8_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_5_3 = cert8_layer_3_5_3 := by
  decide

theorem cert8_component_3_5_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 18 cert8_seen_3_5_0 = cert8_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_5_0 cert8_layer_3_5_0 17 cert8_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 17 cert8_seen_3_5_1 = cert8_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_5_1 cert8_layer_3_5_1 16 cert8_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 16 cert8_seen_3_5_2 = cert8_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_5_2 cert8_layer_3_5_2 15 cert8_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 15 cert8_seen_3_5_3 = cert8_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_5_3 cert8_layer_3_5_3_eq 15

theorem cert8_step_3_5 :
    closedCollarIndexStepBool word fiber8 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_5)
    (by decide) (by decide)
    (by simpa [cert8_move_3_5] using cert8_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_2_0 = cert8_layer_4_2_0 := by
  decide

def cert8_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_2_1 = cert8_layer_4_2_1 := by
  decide

def cert8_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_2_2 = cert8_layer_4_2_2 := by
  decide

def cert8_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_4_2_3 : List ChainEdge :=
  []

theorem cert8_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_2_3 = cert8_layer_4_2_3 := by
  decide

theorem cert8_component_4_2_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 18 cert8_seen_4_2_0 = cert8_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_2_0 cert8_layer_4_2_0 17 cert8_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 17 cert8_seen_4_2_1 = cert8_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_2_1 cert8_layer_4_2_1 16 cert8_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 16 cert8_seen_4_2_2 = cert8_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_2_2 cert8_layer_4_2_2 15 cert8_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 15 cert8_seen_4_2_3 = cert8_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_2_3 cert8_layer_4_2_3_eq 15

theorem cert8_step_4_2 :
    closedCollarIndexStepBool word fiber8 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_2)
    (by decide) (by decide)
    (by simpa [cert8_move_4_2] using cert8_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_3_0 = cert8_layer_5_3_0 := by
  decide

def cert8_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_3_1 = cert8_layer_5_3_1 := by
  decide

def cert8_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_3_2 = cert8_layer_5_3_2 := by
  decide

def cert8_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_5_3_3 : List ChainEdge :=
  []

theorem cert8_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_3_3 = cert8_layer_5_3_3 := by
  decide

theorem cert8_component_5_3_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 18 cert8_seen_5_3_0 = cert8_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_3_0 cert8_layer_5_3_0 17 cert8_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 17 cert8_seen_5_3_1 = cert8_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_3_1 cert8_layer_5_3_1 16 cert8_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 16 cert8_seen_5_3_2 = cert8_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_3_2 cert8_layer_5_3_2 15 cert8_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 15 cert8_seen_5_3_3 = cert8_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_3_3 cert8_layer_5_3_3_eq 15

theorem cert8_step_5_3 :
    closedCollarIndexStepBool word fiber8 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_3)
    (by decide) (by decide)
    (by simpa [cert8_move_5_3] using cert8_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert8_row_0 :
    closedCollarParentIndexValid word fiber8 cert8.parents 0 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length]

theorem cert8_row_1 :
    closedCollarParentIndexValid word fiber8 cert8.parents 1 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_1_0, cert8_step_0_1]

theorem cert8_row_2 :
    closedCollarParentIndexValid word fiber8 cert8.parents 2 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_2_0, cert8_step_0_2]

theorem cert8_row_3 :
    closedCollarParentIndexValid word fiber8 cert8.parents 3 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_3_1, cert8_step_1_3]

theorem cert8_row_4 :
    closedCollarParentIndexValid word fiber8 cert8.parents 4 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_4_2, cert8_step_2_4]

theorem cert8_row_5 :
    closedCollarParentIndexValid word fiber8 cert8.parents 5 = true := by
  have cert8_fiber_length : fiber8.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_5_3, cert8_step_3_5]

theorem cert8_rows :
    closedCollarSpineRowsValid word fiber8 cert8.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert8_fiber_length : fiber8.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert8_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert8_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert8_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert8_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert8_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert8_row_5
  · omega

theorem cert8_root :
    closedCollarSpineParentsReachRoot fiber8 cert8 = true := by
  decide

theorem cert8_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert8.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert8 closedStates_eq fiber8_eq cert8_rows cert8_root

def fiber9 : List (List TauState) :=
[
  [stateAt 114, stateAt 54]
, [stateAt 115, stateAt 62]
]

theorem fiber9_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.r, LColor.r] = fiber9 := by
  decide

def cert9 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.b, LColor.r, LColor.r],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert9_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert9_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert9_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert9_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert9_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber9 0 [])
      LColor.r LColor.b cert9_seen_0_1_0 = cert9_layer_0_1_0 := by
  decide

def cert9_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert9_layer_0_1_1 : List ChainEdge :=
  []

theorem cert9_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber9 0 [])
      LColor.r LColor.b cert9_seen_0_1_1 = cert9_layer_0_1_1 := by
  decide

theorem cert9_component_0_1_eq :
    closedCollarComponent word (listGetD fiber9 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert9_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber9 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber9 0 [])
      LColor.r LColor.b 18 cert9_seen_0_1_0 = cert9_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber9 0 []) LColor.r LColor.b
    cert9_seen_0_1_0 cert9_layer_0_1_0 17 cert9_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber9 0 [])
      LColor.r LColor.b 17 cert9_seen_0_1_1 = cert9_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber9 0 []) LColor.r LColor.b
    cert9_seen_0_1_1 cert9_layer_0_1_1_eq 17

theorem cert9_step_0_1 :
    closedCollarIndexStepBool word fiber9 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert9_move_0_1)
    (by decide) (by decide)
    (by simpa [cert9_move_0_1] using cert9_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert9_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert9_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert9_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert9_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert9_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber9 1 [])
      LColor.r LColor.b cert9_seen_1_0_0 = cert9_layer_1_0_0 := by
  decide

def cert9_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert9_layer_1_0_1 : List ChainEdge :=
  []

theorem cert9_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber9 1 [])
      LColor.r LColor.b cert9_seen_1_0_1 = cert9_layer_1_0_1 := by
  decide

theorem cert9_component_1_0_eq :
    closedCollarComponent word (listGetD fiber9 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert9_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber9 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber9 1 [])
      LColor.r LColor.b 18 cert9_seen_1_0_0 = cert9_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber9 1 []) LColor.r LColor.b
    cert9_seen_1_0_0 cert9_layer_1_0_0 17 cert9_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber9 1 [])
      LColor.r LColor.b 17 cert9_seen_1_0_1 = cert9_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber9 1 []) LColor.r LColor.b
    cert9_seen_1_0_1 cert9_layer_1_0_1_eq 17

theorem cert9_step_1_0 :
    closedCollarIndexStepBool word fiber9 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert9_move_1_0)
    (by decide) (by decide)
    (by simpa [cert9_move_1_0] using cert9_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert9_row_0 :
    closedCollarParentIndexValid word fiber9 cert9.parents 0 = true := by
  have cert9_fiber_length : fiber9.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert9, listGetD, cert9_fiber_length]

theorem cert9_row_1 :
    closedCollarParentIndexValid word fiber9 cert9.parents 1 = true := by
  have cert9_fiber_length : fiber9.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert9, listGetD, cert9_fiber_length, cert9_step_1_0, cert9_step_0_1]

theorem cert9_rows :
    closedCollarSpineRowsValid word fiber9 cert9.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert9_fiber_length : fiber9.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert9_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert9_row_1
  · omega

theorem cert9_root :
    closedCollarSpineParentsReachRoot fiber9 cert9 = true := by
  decide

theorem cert9_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.r, LColor.r] := by
  change closedCollarFiberKempeConnected word cert9.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert9 closedStates_eq fiber9_eq cert9_rows cert9_root

def fiber10 : List (List TauState) :=
[
  [stateAt 2, stateAt 34]
, [stateAt 3, stateAt 42]
, [stateAt 48, stateAt 150]
, [stateAt 49, stateAt 158]
, [stateAt 50, stateAt 50]
, [stateAt 51, stateAt 58]
]

theorem fiber10_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.r, LColor.b] = fiber10 := by
  decide

def cert10 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.b, LColor.r, LColor.b],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 5, 4, 0, 1] }

def cert10_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert10_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert10_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert10_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.r LColor.p cert10_seen_0_1_0 = cert10_layer_0_1_0 := by
  decide

def cert10_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_layer_0_1_1 : List ChainEdge :=
  []

theorem cert10_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.r LColor.p cert10_seen_0_1_1 = cert10_layer_0_1_1 := by
  decide

theorem cert10_component_0_1_eq :
    closedCollarComponent word (listGetD fiber10 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert10_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.r LColor.p 18 cert10_seen_0_1_0 = cert10_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 0 []) LColor.r LColor.p
    cert10_seen_0_1_0 cert10_layer_0_1_0 17 cert10_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.r LColor.p 17 cert10_seen_0_1_1 = cert10_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 0 []) LColor.r LColor.p
    cert10_seen_0_1_1 cert10_layer_0_1_1_eq 17

theorem cert10_step_0_1 :
    closedCollarIndexStepBool word fiber10 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_0_1)
    (by decide) (by decide)
    (by simpa [cert10_move_0_1] using cert10_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert10_move_0_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert10_component_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert10_seen_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert10_layer_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert10_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.b LColor.p cert10_seen_0_4_0 = cert10_layer_0_4_0 := by
  decide

def cert10_seen_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert10_layer_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert10_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.b LColor.p cert10_seen_0_4_1 = cert10_layer_0_4_1 := by
  decide

def cert10_seen_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert10_layer_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert10_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.b LColor.p cert10_seen_0_4_2 = cert10_layer_0_4_2 := by
  decide

def cert10_seen_0_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert10_layer_0_4_3 : List ChainEdge :=
  []

theorem cert10_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 0 [])
      LColor.b LColor.p cert10_seen_0_4_3 = cert10_layer_0_4_3 := by
  decide

theorem cert10_component_0_4_eq :
    closedCollarComponent word (listGetD fiber10 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert10_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.b LColor.p 18 cert10_seen_0_4_0 = cert10_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 0 []) LColor.b LColor.p
    cert10_seen_0_4_0 cert10_layer_0_4_0 17 cert10_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.b LColor.p 17 cert10_seen_0_4_1 = cert10_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 0 []) LColor.b LColor.p
    cert10_seen_0_4_1 cert10_layer_0_4_1 16 cert10_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.b LColor.p 16 cert10_seen_0_4_2 = cert10_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 0 []) LColor.b LColor.p
    cert10_seen_0_4_2 cert10_layer_0_4_2 15 cert10_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 0 [])
      LColor.b LColor.p 15 cert10_seen_0_4_3 = cert10_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 0 []) LColor.b LColor.p
    cert10_seen_0_4_3 cert10_layer_0_4_3_eq 15

theorem cert10_step_0_4 :
    closedCollarIndexStepBool word fiber10 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_0_4)
    (by decide) (by decide)
    (by simpa [cert10_move_0_4] using cert10_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert10_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert10_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert10_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert10_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.r LColor.p cert10_seen_1_0_0 = cert10_layer_1_0_0 := by
  decide

def cert10_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_layer_1_0_1 : List ChainEdge :=
  []

theorem cert10_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.r LColor.p cert10_seen_1_0_1 = cert10_layer_1_0_1 := by
  decide

theorem cert10_component_1_0_eq :
    closedCollarComponent word (listGetD fiber10 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert10_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.r LColor.p 18 cert10_seen_1_0_0 = cert10_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 1 []) LColor.r LColor.p
    cert10_seen_1_0_0 cert10_layer_1_0_0 17 cert10_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.r LColor.p 17 cert10_seen_1_0_1 = cert10_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 1 []) LColor.r LColor.p
    cert10_seen_1_0_1 cert10_layer_1_0_1_eq 17

theorem cert10_step_1_0 :
    closedCollarIndexStepBool word fiber10 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_1_0)
    (by decide) (by decide)
    (by simpa [cert10_move_1_0] using cert10_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert10_move_1_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert10_component_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_seen_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert10_layer_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert10_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.b LColor.p cert10_seen_1_5_0 = cert10_layer_1_5_0 := by
  decide

def cert10_seen_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert10_layer_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert10_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.b LColor.p cert10_seen_1_5_1 = cert10_layer_1_5_1 := by
  decide

def cert10_seen_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert10_layer_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert10_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.b LColor.p cert10_seen_1_5_2 = cert10_layer_1_5_2 := by
  decide

def cert10_seen_1_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_layer_1_5_3 : List ChainEdge :=
  []

theorem cert10_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 1 [])
      LColor.b LColor.p cert10_seen_1_5_3 = cert10_layer_1_5_3 := by
  decide

theorem cert10_component_1_5_eq :
    closedCollarComponent word (listGetD fiber10 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert10_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.b LColor.p 18 cert10_seen_1_5_0 = cert10_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 1 []) LColor.b LColor.p
    cert10_seen_1_5_0 cert10_layer_1_5_0 17 cert10_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.b LColor.p 17 cert10_seen_1_5_1 = cert10_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 1 []) LColor.b LColor.p
    cert10_seen_1_5_1 cert10_layer_1_5_1 16 cert10_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.b LColor.p 16 cert10_seen_1_5_2 = cert10_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 1 []) LColor.b LColor.p
    cert10_seen_1_5_2 cert10_layer_1_5_2 15 cert10_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 1 [])
      LColor.b LColor.p 15 cert10_seen_1_5_3 = cert10_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 1 []) LColor.b LColor.p
    cert10_seen_1_5_3 cert10_layer_1_5_3_eq 15

theorem cert10_step_1_5 :
    closedCollarIndexStepBool word fiber10 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_1_5)
    (by decide) (by decide)
    (by simpa [cert10_move_1_5] using cert10_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert10_move_2_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert10_component_2_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_seen_2_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert10_layer_2_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert10_layer_2_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 2 [])
      LColor.r LColor.p cert10_seen_2_5_0 = cert10_layer_2_5_0 := by
  decide

def cert10_seen_2_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert10_layer_2_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert10_layer_2_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 2 [])
      LColor.r LColor.p cert10_seen_2_5_1 = cert10_layer_2_5_1 := by
  decide

def cert10_seen_2_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert10_layer_2_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert10_layer_2_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 2 [])
      LColor.r LColor.p cert10_seen_2_5_2 = cert10_layer_2_5_2 := by
  decide

def cert10_seen_2_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_layer_2_5_3 : List ChainEdge :=
  []

theorem cert10_layer_2_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 2 [])
      LColor.r LColor.p cert10_seen_2_5_3 = cert10_layer_2_5_3 := by
  decide

theorem cert10_component_2_5_eq :
    closedCollarComponent word (listGetD fiber10 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert10_component_2_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 2 [])
      LColor.r LColor.p 18 cert10_seen_2_5_0 = cert10_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 2 []) LColor.r LColor.p
    cert10_seen_2_5_0 cert10_layer_2_5_0 17 cert10_layer_2_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 2 [])
      LColor.r LColor.p 17 cert10_seen_2_5_1 = cert10_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 2 []) LColor.r LColor.p
    cert10_seen_2_5_1 cert10_layer_2_5_1 16 cert10_layer_2_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 2 [])
      LColor.r LColor.p 16 cert10_seen_2_5_2 = cert10_component_2_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 2 []) LColor.r LColor.p
    cert10_seen_2_5_2 cert10_layer_2_5_2 15 cert10_layer_2_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 2 [])
      LColor.r LColor.p 15 cert10_seen_2_5_3 = cert10_component_2_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 2 []) LColor.r LColor.p
    cert10_seen_2_5_3 cert10_layer_2_5_3_eq 15

theorem cert10_step_2_5 :
    closedCollarIndexStepBool word fiber10 2 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_2_5)
    (by decide) (by decide)
    (by simpa [cert10_move_2_5] using cert10_component_2_5_eq)
    (by decide) (by decide) (by decide)

def cert10_move_3_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert10_component_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_seen_3_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert10_layer_3_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert10_layer_3_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 3 [])
      LColor.r LColor.p cert10_seen_3_4_0 = cert10_layer_3_4_0 := by
  decide

def cert10_seen_3_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert10_layer_3_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert10_layer_3_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 3 [])
      LColor.r LColor.p cert10_seen_3_4_1 = cert10_layer_3_4_1 := by
  decide

def cert10_seen_3_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert10_layer_3_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert10_layer_3_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 3 [])
      LColor.r LColor.p cert10_seen_3_4_2 = cert10_layer_3_4_2 := by
  decide

def cert10_seen_3_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_layer_3_4_3 : List ChainEdge :=
  []

theorem cert10_layer_3_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 3 [])
      LColor.r LColor.p cert10_seen_3_4_3 = cert10_layer_3_4_3 := by
  decide

theorem cert10_component_3_4_eq :
    closedCollarComponent word (listGetD fiber10 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert10_component_3_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 3 [])
      LColor.r LColor.p 18 cert10_seen_3_4_0 = cert10_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 3 []) LColor.r LColor.p
    cert10_seen_3_4_0 cert10_layer_3_4_0 17 cert10_layer_3_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 3 [])
      LColor.r LColor.p 17 cert10_seen_3_4_1 = cert10_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 3 []) LColor.r LColor.p
    cert10_seen_3_4_1 cert10_layer_3_4_1 16 cert10_layer_3_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 3 [])
      LColor.r LColor.p 16 cert10_seen_3_4_2 = cert10_component_3_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 3 []) LColor.r LColor.p
    cert10_seen_3_4_2 cert10_layer_3_4_2 15 cert10_layer_3_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 3 [])
      LColor.r LColor.p 15 cert10_seen_3_4_3 = cert10_component_3_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 3 []) LColor.r LColor.p
    cert10_seen_3_4_3 cert10_layer_3_4_3_eq 15

theorem cert10_step_3_4 :
    closedCollarIndexStepBool word fiber10 3 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_3_4)
    (by decide) (by decide)
    (by simpa [cert10_move_3_4] using cert10_component_3_4_eq)
    (by decide) (by decide) (by decide)

def cert10_move_4_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert10_component_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert10_seen_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert10_layer_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert10_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.b LColor.p cert10_seen_4_0_0 = cert10_layer_4_0_0 := by
  decide

def cert10_seen_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert10_layer_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert10_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.b LColor.p cert10_seen_4_0_1 = cert10_layer_4_0_1 := by
  decide

def cert10_seen_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert10_layer_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert10_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.b LColor.p cert10_seen_4_0_2 = cert10_layer_4_0_2 := by
  decide

def cert10_seen_4_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert10_layer_4_0_3 : List ChainEdge :=
  []

theorem cert10_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.b LColor.p cert10_seen_4_0_3 = cert10_layer_4_0_3 := by
  decide

theorem cert10_component_4_0_eq :
    closedCollarComponent word (listGetD fiber10 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert10_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.b LColor.p 18 cert10_seen_4_0_0 = cert10_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.b LColor.p
    cert10_seen_4_0_0 cert10_layer_4_0_0 17 cert10_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.b LColor.p 17 cert10_seen_4_0_1 = cert10_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.b LColor.p
    cert10_seen_4_0_1 cert10_layer_4_0_1 16 cert10_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.b LColor.p 16 cert10_seen_4_0_2 = cert10_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.b LColor.p
    cert10_seen_4_0_2 cert10_layer_4_0_2 15 cert10_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.b LColor.p 15 cert10_seen_4_0_3 = cert10_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 4 []) LColor.b LColor.p
    cert10_seen_4_0_3 cert10_layer_4_0_3_eq 15

theorem cert10_step_4_0 :
    closedCollarIndexStepBool word fiber10 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_4_0)
    (by decide) (by decide)
    (by simpa [cert10_move_4_0] using cert10_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert10_move_4_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert10_component_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_seen_4_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert10_layer_4_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert10_layer_4_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.r LColor.p cert10_seen_4_3_0 = cert10_layer_4_3_0 := by
  decide

def cert10_seen_4_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert10_layer_4_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert10_layer_4_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.r LColor.p cert10_seen_4_3_1 = cert10_layer_4_3_1 := by
  decide

def cert10_seen_4_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert10_layer_4_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert10_layer_4_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.r LColor.p cert10_seen_4_3_2 = cert10_layer_4_3_2 := by
  decide

def cert10_seen_4_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_layer_4_3_3 : List ChainEdge :=
  []

theorem cert10_layer_4_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 4 [])
      LColor.r LColor.p cert10_seen_4_3_3 = cert10_layer_4_3_3 := by
  decide

theorem cert10_component_4_3_eq :
    closedCollarComponent word (listGetD fiber10 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert10_component_4_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.r LColor.p 18 cert10_seen_4_3_0 = cert10_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.r LColor.p
    cert10_seen_4_3_0 cert10_layer_4_3_0 17 cert10_layer_4_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.r LColor.p 17 cert10_seen_4_3_1 = cert10_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.r LColor.p
    cert10_seen_4_3_1 cert10_layer_4_3_1 16 cert10_layer_4_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.r LColor.p 16 cert10_seen_4_3_2 = cert10_component_4_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 4 []) LColor.r LColor.p
    cert10_seen_4_3_2 cert10_layer_4_3_2 15 cert10_layer_4_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 4 [])
      LColor.r LColor.p 15 cert10_seen_4_3_3 = cert10_component_4_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 4 []) LColor.r LColor.p
    cert10_seen_4_3_3 cert10_layer_4_3_3_eq 15

theorem cert10_step_4_3 :
    closedCollarIndexStepBool word fiber10 4 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_4_3)
    (by decide) (by decide)
    (by simpa [cert10_move_4_3] using cert10_component_4_3_eq)
    (by decide) (by decide) (by decide)

def cert10_move_5_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert10_component_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_seen_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert10_layer_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert10_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.b LColor.p cert10_seen_5_1_0 = cert10_layer_5_1_0 := by
  decide

def cert10_seen_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert10_layer_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert10_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.b LColor.p cert10_seen_5_1_1 = cert10_layer_5_1_1 := by
  decide

def cert10_seen_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert10_layer_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert10_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.b LColor.p cert10_seen_5_1_2 = cert10_layer_5_1_2 := by
  decide

def cert10_seen_5_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert10_layer_5_1_3 : List ChainEdge :=
  []

theorem cert10_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.b LColor.p cert10_seen_5_1_3 = cert10_layer_5_1_3 := by
  decide

theorem cert10_component_5_1_eq :
    closedCollarComponent word (listGetD fiber10 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert10_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.b LColor.p 18 cert10_seen_5_1_0 = cert10_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.b LColor.p
    cert10_seen_5_1_0 cert10_layer_5_1_0 17 cert10_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.b LColor.p 17 cert10_seen_5_1_1 = cert10_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.b LColor.p
    cert10_seen_5_1_1 cert10_layer_5_1_1 16 cert10_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.b LColor.p 16 cert10_seen_5_1_2 = cert10_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.b LColor.p
    cert10_seen_5_1_2 cert10_layer_5_1_2 15 cert10_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.b LColor.p 15 cert10_seen_5_1_3 = cert10_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 5 []) LColor.b LColor.p
    cert10_seen_5_1_3 cert10_layer_5_1_3_eq 15

theorem cert10_step_5_1 :
    closedCollarIndexStepBool word fiber10 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_5_1)
    (by decide) (by decide)
    (by simpa [cert10_move_5_1] using cert10_component_5_1_eq)
    (by decide) (by decide) (by decide)

def cert10_move_5_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert10_component_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_seen_5_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert10_layer_5_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert10_layer_5_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.r LColor.p cert10_seen_5_2_0 = cert10_layer_5_2_0 := by
  decide

def cert10_seen_5_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert10_layer_5_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert10_layer_5_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.r LColor.p cert10_seen_5_2_1 = cert10_layer_5_2_1 := by
  decide

def cert10_seen_5_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert10_layer_5_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert10_layer_5_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.r LColor.p cert10_seen_5_2_2 = cert10_layer_5_2_2 := by
  decide

def cert10_seen_5_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert10_layer_5_2_3 : List ChainEdge :=
  []

theorem cert10_layer_5_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber10 5 [])
      LColor.r LColor.p cert10_seen_5_2_3 = cert10_layer_5_2_3 := by
  decide

theorem cert10_component_5_2_eq :
    closedCollarComponent word (listGetD fiber10 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert10_component_5_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber10 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.r LColor.p 18 cert10_seen_5_2_0 = cert10_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.r LColor.p
    cert10_seen_5_2_0 cert10_layer_5_2_0 17 cert10_layer_5_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.r LColor.p 17 cert10_seen_5_2_1 = cert10_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.r LColor.p
    cert10_seen_5_2_1 cert10_layer_5_2_1 16 cert10_layer_5_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.r LColor.p 16 cert10_seen_5_2_2 = cert10_component_5_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber10 5 []) LColor.r LColor.p
    cert10_seen_5_2_2 cert10_layer_5_2_2 15 cert10_layer_5_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber10 5 [])
      LColor.r LColor.p 15 cert10_seen_5_2_3 = cert10_component_5_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber10 5 []) LColor.r LColor.p
    cert10_seen_5_2_3 cert10_layer_5_2_3_eq 15

theorem cert10_step_5_2 :
    closedCollarIndexStepBool word fiber10 5 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert10_move_5_2)
    (by decide) (by decide)
    (by simpa [cert10_move_5_2] using cert10_component_5_2_eq)
    (by decide) (by decide) (by decide)

theorem cert10_row_0 :
    closedCollarParentIndexValid word fiber10 cert10.parents 0 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length]

theorem cert10_row_1 :
    closedCollarParentIndexValid word fiber10 cert10.parents 1 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length, cert10_step_1_0, cert10_step_0_1]

theorem cert10_row_2 :
    closedCollarParentIndexValid word fiber10 cert10.parents 2 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length, cert10_step_2_5, cert10_step_5_2]

theorem cert10_row_3 :
    closedCollarParentIndexValid word fiber10 cert10.parents 3 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length, cert10_step_3_4, cert10_step_4_3]

theorem cert10_row_4 :
    closedCollarParentIndexValid word fiber10 cert10.parents 4 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length, cert10_step_4_0, cert10_step_0_4]

theorem cert10_row_5 :
    closedCollarParentIndexValid word fiber10 cert10.parents 5 = true := by
  have cert10_fiber_length : fiber10.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert10, listGetD, cert10_fiber_length, cert10_step_5_1, cert10_step_1_5]

theorem cert10_rows :
    closedCollarSpineRowsValid word fiber10 cert10.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert10_fiber_length : fiber10.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert10_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert10_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert10_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert10_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert10_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert10_row_5
  · omega

theorem cert10_root :
    closedCollarSpineParentsReachRoot fiber10 cert10 = true := by
  decide

theorem cert10_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.r, LColor.b] := by
  change closedCollarFiberKempeConnected word cert10.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert10 closedStates_eq fiber10_eq cert10_rows cert10_root

theorem cert11_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.r, LColor.p] = [] := by
  decide

theorem cert11_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert11_empty

theorem cert12_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.b, LColor.r] = [] := by
  decide

theorem cert12_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert12_empty

theorem cert13_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.b, LColor.b] = [] := by
  decide

theorem cert13_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert13_empty

theorem cert14_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.b, LColor.p] = [] := by
  decide

theorem cert14_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert14_empty

theorem cert15_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.p, LColor.r] = [] := by
  decide

theorem cert15_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert15_empty

theorem cert16_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.p, LColor.b] = [] := by
  decide

theorem cert16_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert16_empty

theorem cert17_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.b, LColor.p, LColor.p] = [] := by
  decide

theorem cert17_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert17_empty

def fiber18 : List (List TauState) :=
[
  [stateAt 176, stateAt 22]
, [stateAt 177, stateAt 30]
]

theorem fiber18_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.r, LColor.r] = fiber18 := by
  decide

def cert18 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.p, LColor.r, LColor.r],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert18_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert18_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert18_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert18_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert18_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber18 0 [])
      LColor.r LColor.p cert18_seen_0_1_0 = cert18_layer_0_1_0 := by
  decide

def cert18_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert18_layer_0_1_1 : List ChainEdge :=
  []

theorem cert18_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber18 0 [])
      LColor.r LColor.p cert18_seen_0_1_1 = cert18_layer_0_1_1 := by
  decide

theorem cert18_component_0_1_eq :
    closedCollarComponent word (listGetD fiber18 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert18_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber18 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber18 0 [])
      LColor.r LColor.p 18 cert18_seen_0_1_0 = cert18_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber18 0 []) LColor.r LColor.p
    cert18_seen_0_1_0 cert18_layer_0_1_0 17 cert18_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber18 0 [])
      LColor.r LColor.p 17 cert18_seen_0_1_1 = cert18_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber18 0 []) LColor.r LColor.p
    cert18_seen_0_1_1 cert18_layer_0_1_1_eq 17

theorem cert18_step_0_1 :
    closedCollarIndexStepBool word fiber18 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert18_move_0_1)
    (by decide) (by decide)
    (by simpa [cert18_move_0_1] using cert18_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert18_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert18_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert18_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert18_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert18_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber18 1 [])
      LColor.r LColor.p cert18_seen_1_0_0 = cert18_layer_1_0_0 := by
  decide

def cert18_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert18_layer_1_0_1 : List ChainEdge :=
  []

theorem cert18_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber18 1 [])
      LColor.r LColor.p cert18_seen_1_0_1 = cert18_layer_1_0_1 := by
  decide

theorem cert18_component_1_0_eq :
    closedCollarComponent word (listGetD fiber18 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert18_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber18 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber18 1 [])
      LColor.r LColor.p 18 cert18_seen_1_0_0 = cert18_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber18 1 []) LColor.r LColor.p
    cert18_seen_1_0_0 cert18_layer_1_0_0 17 cert18_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber18 1 [])
      LColor.r LColor.p 17 cert18_seen_1_0_1 = cert18_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber18 1 []) LColor.r LColor.p
    cert18_seen_1_0_1 cert18_layer_1_0_1_eq 17

theorem cert18_step_1_0 :
    closedCollarIndexStepBool word fiber18 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert18_move_1_0)
    (by decide) (by decide)
    (by simpa [cert18_move_1_0] using cert18_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert18_row_0 :
    closedCollarParentIndexValid word fiber18 cert18.parents 0 = true := by
  have cert18_fiber_length : fiber18.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert18, listGetD, cert18_fiber_length]

theorem cert18_row_1 :
    closedCollarParentIndexValid word fiber18 cert18.parents 1 = true := by
  have cert18_fiber_length : fiber18.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert18, listGetD, cert18_fiber_length, cert18_step_1_0, cert18_step_0_1]

theorem cert18_rows :
    closedCollarSpineRowsValid word fiber18 cert18.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert18_fiber_length : fiber18.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert18_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert18_row_1
  · omega

theorem cert18_root :
    closedCollarSpineParentsReachRoot fiber18 cert18 = true := by
  decide

theorem cert18_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.r] := by
  change closedCollarFiberKempeConnected word cert18.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert18 closedStates_eq fiber18_eq cert18_rows cert18_root

theorem cert19_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.r, LColor.b] = [] := by
  decide

theorem cert19_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert19_empty

def fiber20 : List (List TauState) :=
[
  [stateAt 16, stateAt 82]
, [stateAt 17, stateAt 90]
, [stateAt 18, stateAt 18]
, [stateAt 19, stateAt 26]
, [stateAt 34, stateAt 2]
, [stateAt 35, stateAt 10]
]

theorem fiber20_eq :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.r, LColor.p] = fiber20 := by
  decide

def cert20 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.p, LColor.r, LColor.p],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 0, 1, 2, 3] }

def cert20_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_1_0 = cert20_layer_0_1_0 := by
  decide

def cert20_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_0_1_1 : List ChainEdge :=
  []

theorem cert20_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_1_1 = cert20_layer_0_1_1 := by
  decide

theorem cert20_component_0_1_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 18 cert20_seen_0_1_0 = cert20_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_1_0 cert20_layer_0_1_0 17 cert20_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 17 cert20_seen_0_1_1 = cert20_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_1_1 cert20_layer_0_1_1_eq 17

theorem cert20_step_0_1 :
    closedCollarIndexStepBool word fiber20 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_1)
    (by decide) (by decide)
    (by simpa [cert20_move_0_1] using cert20_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_0 = cert20_layer_0_2_0 := by
  decide

def cert20_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_1 = cert20_layer_0_2_1 := by
  decide

def cert20_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_2 = cert20_layer_0_2_2 := by
  decide

def cert20_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_0_2_3 : List ChainEdge :=
  []

theorem cert20_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_3 = cert20_layer_0_2_3 := by
  decide

theorem cert20_component_0_2_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 18 cert20_seen_0_2_0 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_0 cert20_layer_0_2_0 17 cert20_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 17 cert20_seen_0_2_1 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_1 cert20_layer_0_2_1 16 cert20_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 16 cert20_seen_0_2_2 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_2 cert20_layer_0_2_2 15 cert20_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 15 cert20_seen_0_2_3 = cert20_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_3 cert20_layer_0_2_3_eq 15

theorem cert20_step_0_2 :
    closedCollarIndexStepBool word fiber20 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_2)
    (by decide) (by decide)
    (by simpa [cert20_move_0_2] using cert20_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_0_0 = cert20_layer_1_0_0 := by
  decide

def cert20_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_1_0_1 : List ChainEdge :=
  []

theorem cert20_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_0_1 = cert20_layer_1_0_1 := by
  decide

theorem cert20_component_1_0_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 18 cert20_seen_1_0_0 = cert20_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_0_0 cert20_layer_1_0_0 17 cert20_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 17 cert20_seen_1_0_1 = cert20_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_0_1 cert20_layer_1_0_1_eq 17

theorem cert20_step_1_0 :
    closedCollarIndexStepBool word fiber20 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_0)
    (by decide) (by decide)
    (by simpa [cert20_move_1_0] using cert20_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_0 = cert20_layer_1_3_0 := by
  decide

def cert20_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_1 = cert20_layer_1_3_1 := by
  decide

def cert20_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_2 = cert20_layer_1_3_2 := by
  decide

def cert20_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_1_3_3 : List ChainEdge :=
  []

theorem cert20_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_3 = cert20_layer_1_3_3 := by
  decide

theorem cert20_component_1_3_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 18 cert20_seen_1_3_0 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_0 cert20_layer_1_3_0 17 cert20_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 17 cert20_seen_1_3_1 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_1 cert20_layer_1_3_1 16 cert20_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 16 cert20_seen_1_3_2 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_2 cert20_layer_1_3_2 15 cert20_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 15 cert20_seen_1_3_3 = cert20_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_3 cert20_layer_1_3_3_eq 15

theorem cert20_step_1_3 :
    closedCollarIndexStepBool word fiber20 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_3)
    (by decide) (by decide)
    (by simpa [cert20_move_1_3] using cert20_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_0 = cert20_layer_2_0_0 := by
  decide

def cert20_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_1 = cert20_layer_2_0_1 := by
  decide

def cert20_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_2 = cert20_layer_2_0_2 := by
  decide

def cert20_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_2_0_3 : List ChainEdge :=
  []

theorem cert20_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_3 = cert20_layer_2_0_3 := by
  decide

theorem cert20_component_2_0_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 18 cert20_seen_2_0_0 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_0 cert20_layer_2_0_0 17 cert20_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 17 cert20_seen_2_0_1 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_1 cert20_layer_2_0_1 16 cert20_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 16 cert20_seen_2_0_2 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_2 cert20_layer_2_0_2 15 cert20_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 15 cert20_seen_2_0_3 = cert20_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_3 cert20_layer_2_0_3_eq 15

theorem cert20_step_2_0 :
    closedCollarIndexStepBool word fiber20 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_0)
    (by decide) (by decide)
    (by simpa [cert20_move_2_0] using cert20_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_4_0 = cert20_layer_2_4_0 := by
  decide

def cert20_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_4_1 = cert20_layer_2_4_1 := by
  decide

def cert20_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_4_2 = cert20_layer_2_4_2 := by
  decide

def cert20_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_2_4_3 : List ChainEdge :=
  []

theorem cert20_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_4_3 = cert20_layer_2_4_3 := by
  decide

theorem cert20_component_2_4_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 18 cert20_seen_2_4_0 = cert20_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_4_0 cert20_layer_2_4_0 17 cert20_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 17 cert20_seen_2_4_1 = cert20_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_4_1 cert20_layer_2_4_1 16 cert20_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 16 cert20_seen_2_4_2 = cert20_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_4_2 cert20_layer_2_4_2 15 cert20_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 15 cert20_seen_2_4_3 = cert20_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_4_3 cert20_layer_2_4_3_eq 15

theorem cert20_step_2_4 :
    closedCollarIndexStepBool word fiber20 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_4)
    (by decide) (by decide)
    (by simpa [cert20_move_2_4] using cert20_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_0 = cert20_layer_3_1_0 := by
  decide

def cert20_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_1 = cert20_layer_3_1_1 := by
  decide

def cert20_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_2 = cert20_layer_3_1_2 := by
  decide

def cert20_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_3_1_3 : List ChainEdge :=
  []

theorem cert20_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_3 = cert20_layer_3_1_3 := by
  decide

theorem cert20_component_3_1_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 18 cert20_seen_3_1_0 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_0 cert20_layer_3_1_0 17 cert20_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 17 cert20_seen_3_1_1 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_1 cert20_layer_3_1_1 16 cert20_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 16 cert20_seen_3_1_2 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_2 cert20_layer_3_1_2 15 cert20_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 15 cert20_seen_3_1_3 = cert20_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_3 cert20_layer_3_1_3_eq 15

theorem cert20_step_3_1 :
    closedCollarIndexStepBool word fiber20 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_1)
    (by decide) (by decide)
    (by simpa [cert20_move_3_1] using cert20_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_5_0 = cert20_layer_3_5_0 := by
  decide

def cert20_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_5_1 = cert20_layer_3_5_1 := by
  decide

def cert20_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_5_2 = cert20_layer_3_5_2 := by
  decide

def cert20_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_3_5_3 : List ChainEdge :=
  []

theorem cert20_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_5_3 = cert20_layer_3_5_3 := by
  decide

theorem cert20_component_3_5_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 18 cert20_seen_3_5_0 = cert20_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_5_0 cert20_layer_3_5_0 17 cert20_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 17 cert20_seen_3_5_1 = cert20_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_5_1 cert20_layer_3_5_1 16 cert20_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 16 cert20_seen_3_5_2 = cert20_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_5_2 cert20_layer_3_5_2 15 cert20_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 15 cert20_seen_3_5_3 = cert20_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_5_3 cert20_layer_3_5_3_eq 15

theorem cert20_step_3_5 :
    closedCollarIndexStepBool word fiber20 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_5)
    (by decide) (by decide)
    (by simpa [cert20_move_3_5] using cert20_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert20_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_2_0 = cert20_layer_4_2_0 := by
  decide

def cert20_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_2_1 = cert20_layer_4_2_1 := by
  decide

def cert20_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_2_2 = cert20_layer_4_2_2 := by
  decide

def cert20_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_4_2_3 : List ChainEdge :=
  []

theorem cert20_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_2_3 = cert20_layer_4_2_3 := by
  decide

theorem cert20_component_4_2_eq :
    closedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 18 cert20_seen_4_2_0 = cert20_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_2_0 cert20_layer_4_2_0 17 cert20_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 17 cert20_seen_4_2_1 = cert20_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_2_1 cert20_layer_4_2_1 16 cert20_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 16 cert20_seen_4_2_2 = cert20_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_2_2 cert20_layer_4_2_2 15 cert20_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 15 cert20_seen_4_2_3 = cert20_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_2_3 cert20_layer_4_2_3_eq 15

theorem cert20_step_4_2 :
    closedCollarIndexStepBool word fiber20 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_4_2)
    (by decide) (by decide)
    (by simpa [cert20_move_4_2] using cert20_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_3_0 = cert20_layer_5_3_0 := by
  decide

def cert20_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_3_1 = cert20_layer_5_3_1 := by
  decide

def cert20_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_3_2 = cert20_layer_5_3_2 := by
  decide

def cert20_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_5_3_3 : List ChainEdge :=
  []

theorem cert20_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_3_3 = cert20_layer_5_3_3 := by
  decide

theorem cert20_component_5_3_eq :
    closedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 18 cert20_seen_5_3_0 = cert20_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_3_0 cert20_layer_5_3_0 17 cert20_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 17 cert20_seen_5_3_1 = cert20_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_3_1 cert20_layer_5_3_1 16 cert20_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 16 cert20_seen_5_3_2 = cert20_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_3_2 cert20_layer_5_3_2 15 cert20_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 15 cert20_seen_5_3_3 = cert20_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_3_3 cert20_layer_5_3_3_eq 15

theorem cert20_step_5_3 :
    closedCollarIndexStepBool word fiber20 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_5_3)
    (by decide) (by decide)
    (by simpa [cert20_move_5_3] using cert20_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert20_row_0 :
    closedCollarParentIndexValid word fiber20 cert20.parents 0 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length]

theorem cert20_row_1 :
    closedCollarParentIndexValid word fiber20 cert20.parents 1 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_1_0, cert20_step_0_1]

theorem cert20_row_2 :
    closedCollarParentIndexValid word fiber20 cert20.parents 2 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_2_0, cert20_step_0_2]

theorem cert20_row_3 :
    closedCollarParentIndexValid word fiber20 cert20.parents 3 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_3_1, cert20_step_1_3]

theorem cert20_row_4 :
    closedCollarParentIndexValid word fiber20 cert20.parents 4 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_4_2, cert20_step_2_4]

theorem cert20_row_5 :
    closedCollarParentIndexValid word fiber20 cert20.parents 5 = true := by
  have cert20_fiber_length : fiber20.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_5_3, cert20_step_3_5]

theorem cert20_rows :
    closedCollarSpineRowsValid word fiber20 cert20.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert20_fiber_length : fiber20.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert20_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert20_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert20_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert20_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert20_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert20_row_5
  · omega

theorem cert20_root :
    closedCollarSpineParentsReachRoot fiber20 cert20 = true := by
  decide

theorem cert20_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.p] := by
  change closedCollarFiberKempeConnected word cert20.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert20 closedStates_eq fiber20_eq cert20_rows cert20_root

theorem cert21_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.b, LColor.r] = [] := by
  decide

theorem cert21_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert21_empty

theorem cert22_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.b, LColor.b] = [] := by
  decide

theorem cert22_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert22_empty

theorem cert23_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.b, LColor.p] = [] := by
  decide

theorem cert23_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert23_empty

theorem cert24_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.p, LColor.r] = [] := by
  decide

theorem cert24_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert24_empty

theorem cert25_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.p, LColor.b] = [] := by
  decide

theorem cert25_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert25_empty

theorem cert26_empty :
    closedCollarFiberFrom word closedStates [LColor.r, LColor.p, LColor.p, LColor.p] = [] := by
  decide

theorem cert26_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert26_empty

theorem cert27_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.r, LColor.r] = [] := by
  decide

theorem cert27_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert27_empty

theorem cert28_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.r, LColor.b] = [] := by
  decide

theorem cert28_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert28_empty

theorem cert29_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.r, LColor.p] = [] := by
  decide

theorem cert29_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert29_empty

def fiber30 : List (List TauState) :=
[
  [stateAt 72, stateAt 103]
, [stateAt 73, stateAt 111]
, [stateAt 124, stateAt 183]
, [stateAt 125, stateAt 191]
, [stateAt 126, stateAt 119]
, [stateAt 127, stateAt 127]
]

theorem fiber30_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.b, LColor.r] = fiber30 := by
  decide

def cert30 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.r, LColor.b, LColor.r],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 4, 5, 1, 0] }

def cert30_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert30_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert30_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert30_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_1_0 = cert30_layer_0_1_0 := by
  decide

def cert30_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_layer_0_1_1 : List ChainEdge :=
  []

theorem cert30_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_1_1 = cert30_layer_0_1_1 := by
  decide

theorem cert30_component_0_1_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert30_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 18 cert30_seen_0_1_0 = cert30_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_1_0 cert30_layer_0_1_0 17 cert30_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 17 cert30_seen_0_1_1 = cert30_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_1_1 cert30_layer_0_1_1_eq 17

theorem cert30_step_0_1 :
    closedCollarIndexStepBool word fiber30 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_1)
    (by decide) (by decide)
    (by simpa [cert30_move_0_1] using cert30_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_0_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.p cert30_seen_0_5_0 = cert30_layer_0_5_0 := by
  decide

def cert30_seen_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.p cert30_seen_0_5_1 = cert30_layer_0_5_1 := by
  decide

def cert30_seen_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.p cert30_seen_0_5_2 = cert30_layer_0_5_2 := by
  decide

def cert30_seen_0_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_0_5_3 : List ChainEdge :=
  []

theorem cert30_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.p cert30_seen_0_5_3 = cert30_layer_0_5_3 := by
  decide

theorem cert30_component_0_5_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.p 18 cert30_seen_0_5_0 = cert30_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.p
    cert30_seen_0_5_0 cert30_layer_0_5_0 17 cert30_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.p 17 cert30_seen_0_5_1 = cert30_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.p
    cert30_seen_0_5_1 cert30_layer_0_5_1 16 cert30_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.p 16 cert30_seen_0_5_2 = cert30_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.p
    cert30_seen_0_5_2 cert30_layer_0_5_2 15 cert30_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.p 15 cert30_seen_0_5_3 = cert30_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.r LColor.p
    cert30_seen_0_5_3 cert30_layer_0_5_3_eq 15

theorem cert30_step_0_5 :
    closedCollarIndexStepBool word fiber30 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_5)
    (by decide) (by decide)
    (by simpa [cert30_move_0_5] using cert30_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert30_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert30_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert30_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_0_0 = cert30_layer_1_0_0 := by
  decide

def cert30_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_layer_1_0_1 : List ChainEdge :=
  []

theorem cert30_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_0_1 = cert30_layer_1_0_1 := by
  decide

theorem cert30_component_1_0_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert30_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 18 cert30_seen_1_0_0 = cert30_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_0_0 cert30_layer_1_0_0 17 cert30_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 17 cert30_seen_1_0_1 = cert30_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_0_1 cert30_layer_1_0_1_eq 17

theorem cert30_step_1_0 :
    closedCollarIndexStepBool word fiber30 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_0)
    (by decide) (by decide)
    (by simpa [cert30_move_1_0] using cert30_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_seen_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.p cert30_seen_1_4_0 = cert30_layer_1_4_0 := by
  decide

def cert30_seen_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.p cert30_seen_1_4_1 = cert30_layer_1_4_1 := by
  decide

def cert30_seen_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert30_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.p cert30_seen_1_4_2 = cert30_layer_1_4_2 := by
  decide

def cert30_seen_1_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_layer_1_4_3 : List ChainEdge :=
  []

theorem cert30_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.p cert30_seen_1_4_3 = cert30_layer_1_4_3 := by
  decide

theorem cert30_component_1_4_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.p 18 cert30_seen_1_4_0 = cert30_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.p
    cert30_seen_1_4_0 cert30_layer_1_4_0 17 cert30_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.p 17 cert30_seen_1_4_1 = cert30_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.p
    cert30_seen_1_4_1 cert30_layer_1_4_1 16 cert30_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.p 16 cert30_seen_1_4_2 = cert30_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.p
    cert30_seen_1_4_2 cert30_layer_1_4_2 15 cert30_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.p 15 cert30_seen_1_4_3 = cert30_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.r LColor.p
    cert30_seen_1_4_3 cert30_layer_1_4_3_eq 15

theorem cert30_step_1_4 :
    closedCollarIndexStepBool word fiber30 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_4)
    (by decide) (by decide)
    (by simpa [cert30_move_1_4] using cert30_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_0 = cert30_layer_2_4_0 := by
  decide

def cert30_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_1 = cert30_layer_2_4_1 := by
  decide

def cert30_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_2 = cert30_layer_2_4_2 := by
  decide

def cert30_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_2_4_3 : List ChainEdge :=
  []

theorem cert30_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_3 = cert30_layer_2_4_3 := by
  decide

theorem cert30_component_2_4_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 18 cert30_seen_2_4_0 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_0 cert30_layer_2_4_0 17 cert30_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 17 cert30_seen_2_4_1 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_1 cert30_layer_2_4_1 16 cert30_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 16 cert30_seen_2_4_2 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_2 cert30_layer_2_4_2 15 cert30_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 15 cert30_seen_2_4_3 = cert30_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_3 cert30_layer_2_4_3_eq 15

theorem cert30_step_2_4 :
    closedCollarIndexStepBool word fiber30 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_4)
    (by decide) (by decide)
    (by simpa [cert30_move_2_4] using cert30_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_0 = cert30_layer_3_5_0 := by
  decide

def cert30_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_3_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_1 = cert30_layer_3_5_1 := by
  decide

def cert30_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_3_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_2 = cert30_layer_3_5_2 := by
  decide

def cert30_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_3_5_3 : List ChainEdge :=
  []

theorem cert30_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_3 = cert30_layer_3_5_3 := by
  decide

theorem cert30_component_3_5_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 18 cert30_seen_3_5_0 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_0 cert30_layer_3_5_0 17 cert30_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 17 cert30_seen_3_5_1 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_1 cert30_layer_3_5_1 16 cert30_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 16 cert30_seen_3_5_2 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_2 cert30_layer_3_5_2 15 cert30_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 15 cert30_seen_3_5_3 = cert30_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_3 cert30_layer_3_5_3_eq 15

theorem cert30_step_3_5 :
    closedCollarIndexStepBool word fiber30 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_5)
    (by decide) (by decide)
    (by simpa [cert30_move_3_5] using cert30_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert30_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_seen_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.p cert30_seen_4_1_0 = cert30_layer_4_1_0 := by
  decide

def cert30_seen_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.p cert30_seen_4_1_1 = cert30_layer_4_1_1 := by
  decide

def cert30_seen_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert30_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.p cert30_seen_4_1_2 = cert30_layer_4_1_2 := by
  decide

def cert30_seen_4_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert30_layer_4_1_3 : List ChainEdge :=
  []

theorem cert30_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.p cert30_seen_4_1_3 = cert30_layer_4_1_3 := by
  decide

theorem cert30_component_4_1_eq :
    closedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.p 18 cert30_seen_4_1_0 = cert30_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.r LColor.p
    cert30_seen_4_1_0 cert30_layer_4_1_0 17 cert30_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.p 17 cert30_seen_4_1_1 = cert30_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.r LColor.p
    cert30_seen_4_1_1 cert30_layer_4_1_1 16 cert30_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.p 16 cert30_seen_4_1_2 = cert30_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.r LColor.p
    cert30_seen_4_1_2 cert30_layer_4_1_2 15 cert30_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.p 15 cert30_seen_4_1_3 = cert30_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 4 []) LColor.r LColor.p
    cert30_seen_4_1_3 cert30_layer_4_1_3_eq 15

theorem cert30_step_4_1 :
    closedCollarIndexStepBool word fiber30 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_4_1)
    (by decide) (by decide)
    (by simpa [cert30_move_4_1] using cert30_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_0 = cert30_layer_4_2_0 := by
  decide

def cert30_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_1 = cert30_layer_4_2_1 := by
  decide

def cert30_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_2 = cert30_layer_4_2_2 := by
  decide

def cert30_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_4_2_3 : List ChainEdge :=
  []

theorem cert30_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_3 = cert30_layer_4_2_3 := by
  decide

theorem cert30_component_4_2_eq :
    closedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 18 cert30_seen_4_2_0 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_0 cert30_layer_4_2_0 17 cert30_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 17 cert30_seen_4_2_1 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_1 cert30_layer_4_2_1 16 cert30_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 16 cert30_seen_4_2_2 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_2 cert30_layer_4_2_2 15 cert30_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 15 cert30_seen_4_2_3 = cert30_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_3 cert30_layer_4_2_3_eq 15

theorem cert30_step_4_2 :
    closedCollarIndexStepBool word fiber30 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_4_2)
    (by decide) (by decide)
    (by simpa [cert30_move_4_2] using cert30_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.p cert30_seen_5_0_0 = cert30_layer_5_0_0 := by
  decide

def cert30_seen_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.p cert30_seen_5_0_1 = cert30_layer_5_0_1 := by
  decide

def cert30_seen_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.p cert30_seen_5_0_2 = cert30_layer_5_0_2 := by
  decide

def cert30_seen_5_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_5_0_3 : List ChainEdge :=
  []

theorem cert30_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.p cert30_seen_5_0_3 = cert30_layer_5_0_3 := by
  decide

theorem cert30_component_5_0_eq :
    closedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.p 18 cert30_seen_5_0_0 = cert30_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.r LColor.p
    cert30_seen_5_0_0 cert30_layer_5_0_0 17 cert30_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.p 17 cert30_seen_5_0_1 = cert30_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.r LColor.p
    cert30_seen_5_0_1 cert30_layer_5_0_1 16 cert30_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.p 16 cert30_seen_5_0_2 = cert30_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.r LColor.p
    cert30_seen_5_0_2 cert30_layer_5_0_2 15 cert30_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.p 15 cert30_seen_5_0_3 = cert30_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 5 []) LColor.r LColor.p
    cert30_seen_5_0_3 cert30_layer_5_0_3_eq 15

theorem cert30_step_5_0 :
    closedCollarIndexStepBool word fiber30 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_5_0)
    (by decide) (by decide)
    (by simpa [cert30_move_5_0] using cert30_component_5_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_0 = cert30_layer_5_3_0 := by
  decide

def cert30_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_5_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_1 = cert30_layer_5_3_1 := by
  decide

def cert30_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_5_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_2 = cert30_layer_5_3_2 := by
  decide

def cert30_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_5_3_3 : List ChainEdge :=
  []

theorem cert30_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_3 = cert30_layer_5_3_3 := by
  decide

theorem cert30_component_5_3_eq :
    closedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 18 cert30_seen_5_3_0 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_0 cert30_layer_5_3_0 17 cert30_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 17 cert30_seen_5_3_1 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_1 cert30_layer_5_3_1 16 cert30_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 16 cert30_seen_5_3_2 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_2 cert30_layer_5_3_2 15 cert30_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 15 cert30_seen_5_3_3 = cert30_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_3 cert30_layer_5_3_3_eq 15

theorem cert30_step_5_3 :
    closedCollarIndexStepBool word fiber30 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_5_3)
    (by decide) (by decide)
    (by simpa [cert30_move_5_3] using cert30_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert30_row_0 :
    closedCollarParentIndexValid word fiber30 cert30.parents 0 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length]

theorem cert30_row_1 :
    closedCollarParentIndexValid word fiber30 cert30.parents 1 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_1_0, cert30_step_0_1]

theorem cert30_row_2 :
    closedCollarParentIndexValid word fiber30 cert30.parents 2 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_2_4, cert30_step_4_2]

theorem cert30_row_3 :
    closedCollarParentIndexValid word fiber30 cert30.parents 3 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_3_5, cert30_step_5_3]

theorem cert30_row_4 :
    closedCollarParentIndexValid word fiber30 cert30.parents 4 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_4_1, cert30_step_1_4]

theorem cert30_row_5 :
    closedCollarParentIndexValid word fiber30 cert30.parents 5 = true := by
  have cert30_fiber_length : fiber30.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_5_0, cert30_step_0_5]

theorem cert30_rows :
    closedCollarSpineRowsValid word fiber30 cert30.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert30_fiber_length : fiber30.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert30_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert30_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert30_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert30_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert30_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert30_row_5
  · omega

theorem cert30_root :
    closedCollarSpineParentsReachRoot fiber30 cert30 = true := by
  decide

theorem cert30_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.r] := by
  change closedCollarFiberKempeConnected word cert30.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert30 closedStates_eq fiber30_eq cert30_rows cert30_root

def fiber31 : List (List TauState) :=
[
  [stateAt 62, stateAt 115]
, [stateAt 63, stateAt 123]
]

theorem fiber31_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.b, LColor.b] = fiber31 := by
  decide

def cert31 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.r, LColor.b, LColor.b],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert31_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert31_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert31_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert31_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert31_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber31 0 [])
      LColor.r LColor.b cert31_seen_0_1_0 = cert31_layer_0_1_0 := by
  decide

def cert31_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert31_layer_0_1_1 : List ChainEdge :=
  []

theorem cert31_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber31 0 [])
      LColor.r LColor.b cert31_seen_0_1_1 = cert31_layer_0_1_1 := by
  decide

theorem cert31_component_0_1_eq :
    closedCollarComponent word (listGetD fiber31 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert31_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber31 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber31 0 [])
      LColor.r LColor.b 18 cert31_seen_0_1_0 = cert31_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber31 0 []) LColor.r LColor.b
    cert31_seen_0_1_0 cert31_layer_0_1_0 17 cert31_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber31 0 [])
      LColor.r LColor.b 17 cert31_seen_0_1_1 = cert31_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber31 0 []) LColor.r LColor.b
    cert31_seen_0_1_1 cert31_layer_0_1_1_eq 17

theorem cert31_step_0_1 :
    closedCollarIndexStepBool word fiber31 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert31_move_0_1)
    (by decide) (by decide)
    (by simpa [cert31_move_0_1] using cert31_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert31_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert31_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert31_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert31_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert31_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber31 1 [])
      LColor.r LColor.b cert31_seen_1_0_0 = cert31_layer_1_0_0 := by
  decide

def cert31_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert31_layer_1_0_1 : List ChainEdge :=
  []

theorem cert31_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber31 1 [])
      LColor.r LColor.b cert31_seen_1_0_1 = cert31_layer_1_0_1 := by
  decide

theorem cert31_component_1_0_eq :
    closedCollarComponent word (listGetD fiber31 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert31_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber31 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber31 1 [])
      LColor.r LColor.b 18 cert31_seen_1_0_0 = cert31_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber31 1 []) LColor.r LColor.b
    cert31_seen_1_0_0 cert31_layer_1_0_0 17 cert31_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber31 1 [])
      LColor.r LColor.b 17 cert31_seen_1_0_1 = cert31_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber31 1 []) LColor.r LColor.b
    cert31_seen_1_0_1 cert31_layer_1_0_1_eq 17

theorem cert31_step_1_0 :
    closedCollarIndexStepBool word fiber31 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert31_move_1_0)
    (by decide) (by decide)
    (by simpa [cert31_move_1_0] using cert31_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert31_row_0 :
    closedCollarParentIndexValid word fiber31 cert31.parents 0 = true := by
  have cert31_fiber_length : fiber31.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert31, listGetD, cert31_fiber_length]

theorem cert31_row_1 :
    closedCollarParentIndexValid word fiber31 cert31.parents 1 = true := by
  have cert31_fiber_length : fiber31.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert31, listGetD, cert31_fiber_length, cert31_step_1_0, cert31_step_0_1]

theorem cert31_rows :
    closedCollarSpineRowsValid word fiber31 cert31.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert31_fiber_length : fiber31.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert31_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert31_row_1
  · omega

theorem cert31_root :
    closedCollarSpineParentsReachRoot fiber31 cert31 = true := by
  decide

theorem cert31_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.b] := by
  change closedCollarFiberKempeConnected word cert31.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert31 closedStates_eq fiber31_eq cert31_rows cert31_root

theorem cert32_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.b, LColor.p] = [] := by
  decide

theorem cert32_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert32_empty

theorem cert33_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.p, LColor.r] = [] := by
  decide

theorem cert33_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert33_empty

theorem cert34_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.p, LColor.b] = [] := by
  decide

theorem cert34_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert34_empty

theorem cert35_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.r, LColor.p, LColor.p] = [] := by
  decide

theorem cert35_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert35_empty

def fiber36 : List (List TauState) :=
[
  [stateAt 64, stateAt 102]
, [stateAt 65, stateAt 110]
, [stateAt 116, stateAt 182]
, [stateAt 117, stateAt 190]
, [stateAt 118, stateAt 118]
, [stateAt 119, stateAt 126]
]

theorem fiber36_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.r, LColor.r] = fiber36 := by
  decide

def cert36 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.r, LColor.r],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 4, 5, 1, 0] }

def cert36_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert36_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert36_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert36_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.b LColor.p cert36_seen_0_1_0 = cert36_layer_0_1_0 := by
  decide

def cert36_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_layer_0_1_1 : List ChainEdge :=
  []

theorem cert36_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.b LColor.p cert36_seen_0_1_1 = cert36_layer_0_1_1 := by
  decide

theorem cert36_component_0_1_eq :
    closedCollarComponent word (listGetD fiber36 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert36_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.b LColor.p 18 cert36_seen_0_1_0 = cert36_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 0 []) LColor.b LColor.p
    cert36_seen_0_1_0 cert36_layer_0_1_0 17 cert36_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.b LColor.p 17 cert36_seen_0_1_1 = cert36_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 0 []) LColor.b LColor.p
    cert36_seen_0_1_1 cert36_layer_0_1_1_eq 17

theorem cert36_step_0_1 :
    closedCollarIndexStepBool word fiber36 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_0_1)
    (by decide) (by decide)
    (by simpa [cert36_move_0_1] using cert36_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert36_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert36_component_0_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert36_seen_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert36_layer_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert36_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.r LColor.p cert36_seen_0_5_0 = cert36_layer_0_5_0 := by
  decide

def cert36_seen_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert36_layer_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert36_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.r LColor.p cert36_seen_0_5_1 = cert36_layer_0_5_1 := by
  decide

def cert36_seen_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert36_layer_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert36_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.r LColor.p cert36_seen_0_5_2 = cert36_layer_0_5_2 := by
  decide

def cert36_seen_0_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert36_layer_0_5_3 : List ChainEdge :=
  []

theorem cert36_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 0 [])
      LColor.r LColor.p cert36_seen_0_5_3 = cert36_layer_0_5_3 := by
  decide

theorem cert36_component_0_5_eq :
    closedCollarComponent word (listGetD fiber36 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert36_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.r LColor.p 18 cert36_seen_0_5_0 = cert36_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 0 []) LColor.r LColor.p
    cert36_seen_0_5_0 cert36_layer_0_5_0 17 cert36_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.r LColor.p 17 cert36_seen_0_5_1 = cert36_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 0 []) LColor.r LColor.p
    cert36_seen_0_5_1 cert36_layer_0_5_1 16 cert36_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.r LColor.p 16 cert36_seen_0_5_2 = cert36_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 0 []) LColor.r LColor.p
    cert36_seen_0_5_2 cert36_layer_0_5_2 15 cert36_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 0 [])
      LColor.r LColor.p 15 cert36_seen_0_5_3 = cert36_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 0 []) LColor.r LColor.p
    cert36_seen_0_5_3 cert36_layer_0_5_3_eq 15

theorem cert36_step_0_5 :
    closedCollarIndexStepBool word fiber36 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_0_5)
    (by decide) (by decide)
    (by simpa [cert36_move_0_5] using cert36_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert36_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert36_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert36_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert36_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.b LColor.p cert36_seen_1_0_0 = cert36_layer_1_0_0 := by
  decide

def cert36_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_layer_1_0_1 : List ChainEdge :=
  []

theorem cert36_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.b LColor.p cert36_seen_1_0_1 = cert36_layer_1_0_1 := by
  decide

theorem cert36_component_1_0_eq :
    closedCollarComponent word (listGetD fiber36 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert36_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.b LColor.p 18 cert36_seen_1_0_0 = cert36_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 1 []) LColor.b LColor.p
    cert36_seen_1_0_0 cert36_layer_1_0_0 17 cert36_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.b LColor.p 17 cert36_seen_1_0_1 = cert36_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 1 []) LColor.b LColor.p
    cert36_seen_1_0_1 cert36_layer_1_0_1_eq 17

theorem cert36_step_1_0 :
    closedCollarIndexStepBool word fiber36 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_1_0)
    (by decide) (by decide)
    (by simpa [cert36_move_1_0] using cert36_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert36_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert36_component_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_seen_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert36_layer_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert36_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.r LColor.p cert36_seen_1_4_0 = cert36_layer_1_4_0 := by
  decide

def cert36_seen_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert36_layer_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert36_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.r LColor.p cert36_seen_1_4_1 = cert36_layer_1_4_1 := by
  decide

def cert36_seen_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert36_layer_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert36_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.r LColor.p cert36_seen_1_4_2 = cert36_layer_1_4_2 := by
  decide

def cert36_seen_1_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_layer_1_4_3 : List ChainEdge :=
  []

theorem cert36_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 1 [])
      LColor.r LColor.p cert36_seen_1_4_3 = cert36_layer_1_4_3 := by
  decide

theorem cert36_component_1_4_eq :
    closedCollarComponent word (listGetD fiber36 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert36_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.r LColor.p 18 cert36_seen_1_4_0 = cert36_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 1 []) LColor.r LColor.p
    cert36_seen_1_4_0 cert36_layer_1_4_0 17 cert36_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.r LColor.p 17 cert36_seen_1_4_1 = cert36_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 1 []) LColor.r LColor.p
    cert36_seen_1_4_1 cert36_layer_1_4_1 16 cert36_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.r LColor.p 16 cert36_seen_1_4_2 = cert36_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 1 []) LColor.r LColor.p
    cert36_seen_1_4_2 cert36_layer_1_4_2 15 cert36_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 1 [])
      LColor.r LColor.p 15 cert36_seen_1_4_3 = cert36_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 1 []) LColor.r LColor.p
    cert36_seen_1_4_3 cert36_layer_1_4_3_eq 15

theorem cert36_step_1_4 :
    closedCollarIndexStepBool word fiber36 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_1_4)
    (by decide) (by decide)
    (by simpa [cert36_move_1_4] using cert36_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert36_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert36_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert36_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert36_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 2 [])
      LColor.b LColor.p cert36_seen_2_4_0 = cert36_layer_2_4_0 := by
  decide

def cert36_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert36_layer_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert36_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 2 [])
      LColor.b LColor.p cert36_seen_2_4_1 = cert36_layer_2_4_1 := by
  decide

def cert36_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert36_layer_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert36_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 2 [])
      LColor.b LColor.p cert36_seen_2_4_2 = cert36_layer_2_4_2 := by
  decide

def cert36_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_layer_2_4_3 : List ChainEdge :=
  []

theorem cert36_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 2 [])
      LColor.b LColor.p cert36_seen_2_4_3 = cert36_layer_2_4_3 := by
  decide

theorem cert36_component_2_4_eq :
    closedCollarComponent word (listGetD fiber36 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert36_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 2 [])
      LColor.b LColor.p 18 cert36_seen_2_4_0 = cert36_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 2 []) LColor.b LColor.p
    cert36_seen_2_4_0 cert36_layer_2_4_0 17 cert36_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 2 [])
      LColor.b LColor.p 17 cert36_seen_2_4_1 = cert36_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 2 []) LColor.b LColor.p
    cert36_seen_2_4_1 cert36_layer_2_4_1 16 cert36_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 2 [])
      LColor.b LColor.p 16 cert36_seen_2_4_2 = cert36_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 2 []) LColor.b LColor.p
    cert36_seen_2_4_2 cert36_layer_2_4_2 15 cert36_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 2 [])
      LColor.b LColor.p 15 cert36_seen_2_4_3 = cert36_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 2 []) LColor.b LColor.p
    cert36_seen_2_4_3 cert36_layer_2_4_3_eq 15

theorem cert36_step_2_4 :
    closedCollarIndexStepBool word fiber36 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_2_4)
    (by decide) (by decide)
    (by simpa [cert36_move_2_4] using cert36_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert36_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert36_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert36_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert36_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 3 [])
      LColor.b LColor.p cert36_seen_3_5_0 = cert36_layer_3_5_0 := by
  decide

def cert36_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert36_layer_3_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert36_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 3 [])
      LColor.b LColor.p cert36_seen_3_5_1 = cert36_layer_3_5_1 := by
  decide

def cert36_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert36_layer_3_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert36_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 3 [])
      LColor.b LColor.p cert36_seen_3_5_2 = cert36_layer_3_5_2 := by
  decide

def cert36_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_layer_3_5_3 : List ChainEdge :=
  []

theorem cert36_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 3 [])
      LColor.b LColor.p cert36_seen_3_5_3 = cert36_layer_3_5_3 := by
  decide

theorem cert36_component_3_5_eq :
    closedCollarComponent word (listGetD fiber36 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert36_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 3 [])
      LColor.b LColor.p 18 cert36_seen_3_5_0 = cert36_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 3 []) LColor.b LColor.p
    cert36_seen_3_5_0 cert36_layer_3_5_0 17 cert36_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 3 [])
      LColor.b LColor.p 17 cert36_seen_3_5_1 = cert36_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 3 []) LColor.b LColor.p
    cert36_seen_3_5_1 cert36_layer_3_5_1 16 cert36_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 3 [])
      LColor.b LColor.p 16 cert36_seen_3_5_2 = cert36_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 3 []) LColor.b LColor.p
    cert36_seen_3_5_2 cert36_layer_3_5_2 15 cert36_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 3 [])
      LColor.b LColor.p 15 cert36_seen_3_5_3 = cert36_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 3 []) LColor.b LColor.p
    cert36_seen_3_5_3 cert36_layer_3_5_3_eq 15

theorem cert36_step_3_5 :
    closedCollarIndexStepBool word fiber36 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_3_5)
    (by decide) (by decide)
    (by simpa [cert36_move_3_5] using cert36_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert36_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert36_component_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_seen_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert36_layer_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert36_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.r LColor.p cert36_seen_4_1_0 = cert36_layer_4_1_0 := by
  decide

def cert36_seen_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert36_layer_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert36_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.r LColor.p cert36_seen_4_1_1 = cert36_layer_4_1_1 := by
  decide

def cert36_seen_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert36_layer_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert36_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.r LColor.p cert36_seen_4_1_2 = cert36_layer_4_1_2 := by
  decide

def cert36_seen_4_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert36_layer_4_1_3 : List ChainEdge :=
  []

theorem cert36_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.r LColor.p cert36_seen_4_1_3 = cert36_layer_4_1_3 := by
  decide

theorem cert36_component_4_1_eq :
    closedCollarComponent word (listGetD fiber36 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert36_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.r LColor.p 18 cert36_seen_4_1_0 = cert36_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.r LColor.p
    cert36_seen_4_1_0 cert36_layer_4_1_0 17 cert36_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.r LColor.p 17 cert36_seen_4_1_1 = cert36_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.r LColor.p
    cert36_seen_4_1_1 cert36_layer_4_1_1 16 cert36_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.r LColor.p 16 cert36_seen_4_1_2 = cert36_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.r LColor.p
    cert36_seen_4_1_2 cert36_layer_4_1_2 15 cert36_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.r LColor.p 15 cert36_seen_4_1_3 = cert36_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 4 []) LColor.r LColor.p
    cert36_seen_4_1_3 cert36_layer_4_1_3_eq 15

theorem cert36_step_4_1 :
    closedCollarIndexStepBool word fiber36 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_4_1)
    (by decide) (by decide)
    (by simpa [cert36_move_4_1] using cert36_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert36_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert36_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert36_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert36_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.b LColor.p cert36_seen_4_2_0 = cert36_layer_4_2_0 := by
  decide

def cert36_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert36_layer_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert36_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.b LColor.p cert36_seen_4_2_1 = cert36_layer_4_2_1 := by
  decide

def cert36_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert36_layer_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert36_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.b LColor.p cert36_seen_4_2_2 = cert36_layer_4_2_2 := by
  decide

def cert36_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_layer_4_2_3 : List ChainEdge :=
  []

theorem cert36_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 4 [])
      LColor.b LColor.p cert36_seen_4_2_3 = cert36_layer_4_2_3 := by
  decide

theorem cert36_component_4_2_eq :
    closedCollarComponent word (listGetD fiber36 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert36_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.b LColor.p 18 cert36_seen_4_2_0 = cert36_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.b LColor.p
    cert36_seen_4_2_0 cert36_layer_4_2_0 17 cert36_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.b LColor.p 17 cert36_seen_4_2_1 = cert36_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.b LColor.p
    cert36_seen_4_2_1 cert36_layer_4_2_1 16 cert36_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.b LColor.p 16 cert36_seen_4_2_2 = cert36_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 4 []) LColor.b LColor.p
    cert36_seen_4_2_2 cert36_layer_4_2_2 15 cert36_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 4 [])
      LColor.b LColor.p 15 cert36_seen_4_2_3 = cert36_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 4 []) LColor.b LColor.p
    cert36_seen_4_2_3 cert36_layer_4_2_3_eq 15

theorem cert36_step_4_2 :
    closedCollarIndexStepBool word fiber36 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_4_2)
    (by decide) (by decide)
    (by simpa [cert36_move_4_2] using cert36_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert36_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert36_component_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert36_seen_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert36_layer_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert36_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.r LColor.p cert36_seen_5_0_0 = cert36_layer_5_0_0 := by
  decide

def cert36_seen_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert36_layer_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert36_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.r LColor.p cert36_seen_5_0_1 = cert36_layer_5_0_1 := by
  decide

def cert36_seen_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert36_layer_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert36_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.r LColor.p cert36_seen_5_0_2 = cert36_layer_5_0_2 := by
  decide

def cert36_seen_5_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert36_layer_5_0_3 : List ChainEdge :=
  []

theorem cert36_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.r LColor.p cert36_seen_5_0_3 = cert36_layer_5_0_3 := by
  decide

theorem cert36_component_5_0_eq :
    closedCollarComponent word (listGetD fiber36 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert36_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.r LColor.p 18 cert36_seen_5_0_0 = cert36_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.r LColor.p
    cert36_seen_5_0_0 cert36_layer_5_0_0 17 cert36_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.r LColor.p 17 cert36_seen_5_0_1 = cert36_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.r LColor.p
    cert36_seen_5_0_1 cert36_layer_5_0_1 16 cert36_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.r LColor.p 16 cert36_seen_5_0_2 = cert36_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.r LColor.p
    cert36_seen_5_0_2 cert36_layer_5_0_2 15 cert36_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.r LColor.p 15 cert36_seen_5_0_3 = cert36_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 5 []) LColor.r LColor.p
    cert36_seen_5_0_3 cert36_layer_5_0_3_eq 15

theorem cert36_step_5_0 :
    closedCollarIndexStepBool word fiber36 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_5_0)
    (by decide) (by decide)
    (by simpa [cert36_move_5_0] using cert36_component_5_0_eq)
    (by decide) (by decide) (by decide)

def cert36_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert36_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert36_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert36_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.b LColor.p cert36_seen_5_3_0 = cert36_layer_5_3_0 := by
  decide

def cert36_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert36_layer_5_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert36_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.b LColor.p cert36_seen_5_3_1 = cert36_layer_5_3_1 := by
  decide

def cert36_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert36_layer_5_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert36_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.b LColor.p cert36_seen_5_3_2 = cert36_layer_5_3_2 := by
  decide

def cert36_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert36_layer_5_3_3 : List ChainEdge :=
  []

theorem cert36_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber36 5 [])
      LColor.b LColor.p cert36_seen_5_3_3 = cert36_layer_5_3_3 := by
  decide

theorem cert36_component_5_3_eq :
    closedCollarComponent word (listGetD fiber36 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert36_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber36 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.b LColor.p 18 cert36_seen_5_3_0 = cert36_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.b LColor.p
    cert36_seen_5_3_0 cert36_layer_5_3_0 17 cert36_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.b LColor.p 17 cert36_seen_5_3_1 = cert36_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.b LColor.p
    cert36_seen_5_3_1 cert36_layer_5_3_1 16 cert36_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.b LColor.p 16 cert36_seen_5_3_2 = cert36_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber36 5 []) LColor.b LColor.p
    cert36_seen_5_3_2 cert36_layer_5_3_2 15 cert36_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber36 5 [])
      LColor.b LColor.p 15 cert36_seen_5_3_3 = cert36_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber36 5 []) LColor.b LColor.p
    cert36_seen_5_3_3 cert36_layer_5_3_3_eq 15

theorem cert36_step_5_3 :
    closedCollarIndexStepBool word fiber36 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert36_move_5_3)
    (by decide) (by decide)
    (by simpa [cert36_move_5_3] using cert36_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert36_row_0 :
    closedCollarParentIndexValid word fiber36 cert36.parents 0 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length]

theorem cert36_row_1 :
    closedCollarParentIndexValid word fiber36 cert36.parents 1 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length, cert36_step_1_0, cert36_step_0_1]

theorem cert36_row_2 :
    closedCollarParentIndexValid word fiber36 cert36.parents 2 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length, cert36_step_2_4, cert36_step_4_2]

theorem cert36_row_3 :
    closedCollarParentIndexValid word fiber36 cert36.parents 3 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length, cert36_step_3_5, cert36_step_5_3]

theorem cert36_row_4 :
    closedCollarParentIndexValid word fiber36 cert36.parents 4 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length, cert36_step_4_1, cert36_step_1_4]

theorem cert36_row_5 :
    closedCollarParentIndexValid word fiber36 cert36.parents 5 = true := by
  have cert36_fiber_length : fiber36.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert36, listGetD, cert36_fiber_length, cert36_step_5_0, cert36_step_0_5]

theorem cert36_rows :
    closedCollarSpineRowsValid word fiber36 cert36.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert36_fiber_length : fiber36.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert36_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert36_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert36_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert36_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert36_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert36_row_5
  · omega

theorem cert36_root :
    closedCollarSpineParentsReachRoot fiber36 cert36 = true := by
  decide

theorem cert36_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.r, LColor.r] := by
  change closedCollarFiberKempeConnected word cert36.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert36 closedStates_eq fiber36_eq cert36_rows cert36_root

def fiber37 : List (List TauState) :=
[
  [stateAt 54, stateAt 114]
, [stateAt 55, stateAt 122]
]

theorem fiber37_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.r, LColor.b] = fiber37 := by
  decide

def cert37 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.r, LColor.b],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert37_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert37_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert37_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert37_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert37_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber37 0 [])
      LColor.r LColor.b cert37_seen_0_1_0 = cert37_layer_0_1_0 := by
  decide

def cert37_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert37_layer_0_1_1 : List ChainEdge :=
  []

theorem cert37_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber37 0 [])
      LColor.r LColor.b cert37_seen_0_1_1 = cert37_layer_0_1_1 := by
  decide

theorem cert37_component_0_1_eq :
    closedCollarComponent word (listGetD fiber37 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert37_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber37 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber37 0 [])
      LColor.r LColor.b 18 cert37_seen_0_1_0 = cert37_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber37 0 []) LColor.r LColor.b
    cert37_seen_0_1_0 cert37_layer_0_1_0 17 cert37_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber37 0 [])
      LColor.r LColor.b 17 cert37_seen_0_1_1 = cert37_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber37 0 []) LColor.r LColor.b
    cert37_seen_0_1_1 cert37_layer_0_1_1_eq 17

theorem cert37_step_0_1 :
    closedCollarIndexStepBool word fiber37 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert37_move_0_1)
    (by decide) (by decide)
    (by simpa [cert37_move_0_1] using cert37_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert37_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.B6 } }

def cert37_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert37_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert37_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert37_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber37 1 [])
      LColor.r LColor.b cert37_seen_1_0_0 = cert37_layer_1_0_0 := by
  decide

def cert37_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert37_layer_1_0_1 : List ChainEdge :=
  []

theorem cert37_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber37 1 [])
      LColor.r LColor.b cert37_seen_1_0_1 = cert37_layer_1_0_1 := by
  decide

theorem cert37_component_1_0_eq :
    closedCollarComponent word (listGetD fiber37 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = cert37_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber37 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber37 1 [])
      LColor.r LColor.b 18 cert37_seen_1_0_0 = cert37_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber37 1 []) LColor.r LColor.b
    cert37_seen_1_0_0 cert37_layer_1_0_0 17 cert37_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber37 1 [])
      LColor.r LColor.b 17 cert37_seen_1_0_1 = cert37_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber37 1 []) LColor.r LColor.b
    cert37_seen_1_0_1 cert37_layer_1_0_1_eq 17

theorem cert37_step_1_0 :
    closedCollarIndexStepBool word fiber37 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert37_move_1_0)
    (by decide) (by decide)
    (by simpa [cert37_move_1_0] using cert37_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert37_row_0 :
    closedCollarParentIndexValid word fiber37 cert37.parents 0 = true := by
  have cert37_fiber_length : fiber37.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert37, listGetD, cert37_fiber_length]

theorem cert37_row_1 :
    closedCollarParentIndexValid word fiber37 cert37.parents 1 = true := by
  have cert37_fiber_length : fiber37.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert37, listGetD, cert37_fiber_length, cert37_step_1_0, cert37_step_0_1]

theorem cert37_rows :
    closedCollarSpineRowsValid word fiber37 cert37.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert37_fiber_length : fiber37.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert37_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert37_row_1
  · omega

theorem cert37_root :
    closedCollarSpineParentsReachRoot fiber37 cert37 = true := by
  decide

theorem cert37_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.r, LColor.b] := by
  change closedCollarFiberKempeConnected word cert37.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert37 closedStates_eq fiber37_eq cert37_rows cert37_root

theorem cert38_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.r, LColor.p] = [] := by
  decide

theorem cert38_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert38_empty

theorem cert39_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.b, LColor.r] = [] := by
  decide

theorem cert39_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert39_empty

theorem cert40_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.b, LColor.b] = [] := by
  decide

theorem cert40_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert40_empty

theorem cert41_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.b, LColor.p] = [] := by
  decide

theorem cert41_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert41_empty

theorem cert42_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.p, LColor.r] = [] := by
  decide

theorem cert42_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert42_empty

def fiber43 : List (List TauState) :=
[
  [stateAt 152, stateAt 85]
, [stateAt 153, stateAt 93]
]

theorem fiber43_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.p, LColor.b] = fiber43 := by
  decide

def cert43 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.p, LColor.b],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert43_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert43_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert43_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert43_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert43_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber43 0 [])
      LColor.b LColor.p cert43_seen_0_1_0 = cert43_layer_0_1_0 := by
  decide

def cert43_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert43_layer_0_1_1 : List ChainEdge :=
  []

theorem cert43_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber43 0 [])
      LColor.b LColor.p cert43_seen_0_1_1 = cert43_layer_0_1_1 := by
  decide

theorem cert43_component_0_1_eq :
    closedCollarComponent word (listGetD fiber43 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert43_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber43 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber43 0 [])
      LColor.b LColor.p 18 cert43_seen_0_1_0 = cert43_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber43 0 []) LColor.b LColor.p
    cert43_seen_0_1_0 cert43_layer_0_1_0 17 cert43_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber43 0 [])
      LColor.b LColor.p 17 cert43_seen_0_1_1 = cert43_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber43 0 []) LColor.b LColor.p
    cert43_seen_0_1_1 cert43_layer_0_1_1_eq 17

theorem cert43_step_0_1 :
    closedCollarIndexStepBool word fiber43 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert43_move_0_1)
    (by decide) (by decide)
    (by simpa [cert43_move_0_1] using cert43_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert43_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert43_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert43_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert43_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert43_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber43 1 [])
      LColor.b LColor.p cert43_seen_1_0_0 = cert43_layer_1_0_0 := by
  decide

def cert43_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert43_layer_1_0_1 : List ChainEdge :=
  []

theorem cert43_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber43 1 [])
      LColor.b LColor.p cert43_seen_1_0_1 = cert43_layer_1_0_1 := by
  decide

theorem cert43_component_1_0_eq :
    closedCollarComponent word (listGetD fiber43 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert43_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber43 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber43 1 [])
      LColor.b LColor.p 18 cert43_seen_1_0_0 = cert43_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber43 1 []) LColor.b LColor.p
    cert43_seen_1_0_0 cert43_layer_1_0_0 17 cert43_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber43 1 [])
      LColor.b LColor.p 17 cert43_seen_1_0_1 = cert43_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber43 1 []) LColor.b LColor.p
    cert43_seen_1_0_1 cert43_layer_1_0_1_eq 17

theorem cert43_step_1_0 :
    closedCollarIndexStepBool word fiber43 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert43_move_1_0)
    (by decide) (by decide)
    (by simpa [cert43_move_1_0] using cert43_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert43_row_0 :
    closedCollarParentIndexValid word fiber43 cert43.parents 0 = true := by
  have cert43_fiber_length : fiber43.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert43, listGetD, cert43_fiber_length]

theorem cert43_row_1 :
    closedCollarParentIndexValid word fiber43 cert43.parents 1 = true := by
  have cert43_fiber_length : fiber43.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert43, listGetD, cert43_fiber_length, cert43_step_1_0, cert43_step_0_1]

theorem cert43_rows :
    closedCollarSpineRowsValid word fiber43 cert43.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert43_fiber_length : fiber43.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert43_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert43_row_1
  · omega

theorem cert43_root :
    closedCollarSpineParentsReachRoot fiber43 cert43 = true := by
  decide

theorem cert43_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.b] := by
  change closedCollarFiberKempeConnected word cert43.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert43 closedStates_eq fiber43_eq cert43_rows cert43_root

def fiber44 : List (List TauState) :=
[
  [stateAt 88, stateAt 81]
, [stateAt 89, stateAt 89]
, [stateAt 90, stateAt 17]
, [stateAt 91, stateAt 25]
, [stateAt 110, stateAt 65]
, [stateAt 111, stateAt 73]
]

theorem fiber44_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.b, LColor.p, LColor.p] = fiber44 := by
  decide

def cert44 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.p, LColor.p],
    root := 0,
    maxDepth := 2,
    parents := [0, 0, 0, 1, 1, 0] }

def cert44_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_1_0 = cert44_layer_0_1_0 := by
  decide

def cert44_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_0_1_1 : List ChainEdge :=
  []

theorem cert44_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_1_1 = cert44_layer_0_1_1 := by
  decide

theorem cert44_component_0_1_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 18 cert44_seen_0_1_0 = cert44_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_1_0 cert44_layer_0_1_0 17 cert44_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 17 cert44_seen_0_1_1 = cert44_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_1_1 cert44_layer_0_1_1_eq 17

theorem cert44_step_0_1 :
    closedCollarIndexStepBool word fiber44 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_1)
    (by decide) (by decide)
    (by simpa [cert44_move_0_1] using cert44_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_2_0 = cert44_layer_0_2_0 := by
  decide

def cert44_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_2_1 = cert44_layer_0_2_1 := by
  decide

def cert44_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_2_2 = cert44_layer_0_2_2 := by
  decide

def cert44_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_0_2_3 : List ChainEdge :=
  []

theorem cert44_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_2_3 = cert44_layer_0_2_3 := by
  decide

theorem cert44_component_0_2_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 18 cert44_seen_0_2_0 = cert44_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_2_0 cert44_layer_0_2_0 17 cert44_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 17 cert44_seen_0_2_1 = cert44_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_2_1 cert44_layer_0_2_1 16 cert44_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 16 cert44_seen_0_2_2 = cert44_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_2_2 cert44_layer_0_2_2 15 cert44_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 15 cert44_seen_0_2_3 = cert44_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_2_3 cert44_layer_0_2_3_eq 15

theorem cert44_step_0_2 :
    closedCollarIndexStepBool word fiber44 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_2)
    (by decide) (by decide)
    (by simpa [cert44_move_0_2] using cert44_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_0_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_5_0 = cert44_layer_0_5_0 := by
  decide

def cert44_seen_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_5_1 = cert44_layer_0_5_1 := by
  decide

def cert44_seen_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_5_2 = cert44_layer_0_5_2 := by
  decide

def cert44_seen_0_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_0_5_3 : List ChainEdge :=
  []

theorem cert44_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_5_3 = cert44_layer_0_5_3 := by
  decide

theorem cert44_component_0_5_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 18 cert44_seen_0_5_0 = cert44_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_5_0 cert44_layer_0_5_0 17 cert44_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 17 cert44_seen_0_5_1 = cert44_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_5_1 cert44_layer_0_5_1 16 cert44_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 16 cert44_seen_0_5_2 = cert44_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_5_2 cert44_layer_0_5_2 15 cert44_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 15 cert44_seen_0_5_3 = cert44_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_5_3 cert44_layer_0_5_3_eq 15

theorem cert44_step_0_5 :
    closedCollarIndexStepBool word fiber44 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_5)
    (by decide) (by decide)
    (by simpa [cert44_move_0_5] using cert44_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_0_0 = cert44_layer_1_0_0 := by
  decide

def cert44_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_1_0_1 : List ChainEdge :=
  []

theorem cert44_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_0_1 = cert44_layer_1_0_1 := by
  decide

theorem cert44_component_1_0_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 18 cert44_seen_1_0_0 = cert44_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_0_0 cert44_layer_1_0_0 17 cert44_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 17 cert44_seen_1_0_1 = cert44_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_0_1 cert44_layer_1_0_1_eq 17

theorem cert44_step_1_0 :
    closedCollarIndexStepBool word fiber44 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_0)
    (by decide) (by decide)
    (by simpa [cert44_move_1_0] using cert44_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_3_0 = cert44_layer_1_3_0 := by
  decide

def cert44_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_3_1 = cert44_layer_1_3_1 := by
  decide

def cert44_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_3_2 = cert44_layer_1_3_2 := by
  decide

def cert44_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_1_3_3 : List ChainEdge :=
  []

theorem cert44_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_3_3 = cert44_layer_1_3_3 := by
  decide

theorem cert44_component_1_3_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 18 cert44_seen_1_3_0 = cert44_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_3_0 cert44_layer_1_3_0 17 cert44_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 17 cert44_seen_1_3_1 = cert44_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_3_1 cert44_layer_1_3_1 16 cert44_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 16 cert44_seen_1_3_2 = cert44_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_3_2 cert44_layer_1_3_2 15 cert44_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 15 cert44_seen_1_3_3 = cert44_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_3_3 cert44_layer_1_3_3_eq 15

theorem cert44_step_1_3 :
    closedCollarIndexStepBool word fiber44 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_3)
    (by decide) (by decide)
    (by simpa [cert44_move_1_3] using cert44_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_4_0 = cert44_layer_1_4_0 := by
  decide

def cert44_seen_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_4_1 = cert44_layer_1_4_1 := by
  decide

def cert44_seen_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_4_2 = cert44_layer_1_4_2 := by
  decide

def cert44_seen_1_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_1_4_3 : List ChainEdge :=
  []

theorem cert44_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_4_3 = cert44_layer_1_4_3 := by
  decide

theorem cert44_component_1_4_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 18 cert44_seen_1_4_0 = cert44_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_4_0 cert44_layer_1_4_0 17 cert44_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 17 cert44_seen_1_4_1 = cert44_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_4_1 cert44_layer_1_4_1 16 cert44_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 16 cert44_seen_1_4_2 = cert44_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_4_2 cert44_layer_1_4_2 15 cert44_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 15 cert44_seen_1_4_3 = cert44_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_4_3 cert44_layer_1_4_3_eq 15

theorem cert44_step_1_4 :
    closedCollarIndexStepBool word fiber44 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_4)
    (by decide) (by decide)
    (by simpa [cert44_move_1_4] using cert44_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_0_0 = cert44_layer_2_0_0 := by
  decide

def cert44_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_0_1 = cert44_layer_2_0_1 := by
  decide

def cert44_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_0_2 = cert44_layer_2_0_2 := by
  decide

def cert44_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_2_0_3 : List ChainEdge :=
  []

theorem cert44_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_0_3 = cert44_layer_2_0_3 := by
  decide

theorem cert44_component_2_0_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 18 cert44_seen_2_0_0 = cert44_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_0_0 cert44_layer_2_0_0 17 cert44_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 17 cert44_seen_2_0_1 = cert44_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_0_1 cert44_layer_2_0_1 16 cert44_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 16 cert44_seen_2_0_2 = cert44_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_0_2 cert44_layer_2_0_2 15 cert44_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 15 cert44_seen_2_0_3 = cert44_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_0_3 cert44_layer_2_0_3_eq 15

theorem cert44_step_2_0 :
    closedCollarIndexStepBool word fiber44 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_0)
    (by decide) (by decide)
    (by simpa [cert44_move_2_0] using cert44_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_1_0 = cert44_layer_3_1_0 := by
  decide

def cert44_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_1_1 = cert44_layer_3_1_1 := by
  decide

def cert44_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_1_2 = cert44_layer_3_1_2 := by
  decide

def cert44_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_3_1_3 : List ChainEdge :=
  []

theorem cert44_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_1_3 = cert44_layer_3_1_3 := by
  decide

theorem cert44_component_3_1_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 18 cert44_seen_3_1_0 = cert44_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_1_0 cert44_layer_3_1_0 17 cert44_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 17 cert44_seen_3_1_1 = cert44_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_1_1 cert44_layer_3_1_1 16 cert44_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 16 cert44_seen_3_1_2 = cert44_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_1_2 cert44_layer_3_1_2 15 cert44_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 15 cert44_seen_3_1_3 = cert44_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_1_3 cert44_layer_3_1_3_eq 15

theorem cert44_step_3_1 :
    closedCollarIndexStepBool word fiber44 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_1)
    (by decide) (by decide)
    (by simpa [cert44_move_3_1] using cert44_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_1_0 = cert44_layer_4_1_0 := by
  decide

def cert44_seen_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_1_1 = cert44_layer_4_1_1 := by
  decide

def cert44_seen_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_1_2 = cert44_layer_4_1_2 := by
  decide

def cert44_seen_4_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_4_1_3 : List ChainEdge :=
  []

theorem cert44_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_1_3 = cert44_layer_4_1_3 := by
  decide

theorem cert44_component_4_1_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 18 cert44_seen_4_1_0 = cert44_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_1_0 cert44_layer_4_1_0 17 cert44_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 17 cert44_seen_4_1_1 = cert44_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_1_1 cert44_layer_4_1_1 16 cert44_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 16 cert44_seen_4_1_2 = cert44_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_1_2 cert44_layer_4_1_2 15 cert44_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 15 cert44_seen_4_1_3 = cert44_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_1_3 cert44_layer_4_1_3_eq 15

theorem cert44_step_4_1 :
    closedCollarIndexStepBool word fiber44 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_1)
    (by decide) (by decide)
    (by simpa [cert44_move_4_1] using cert44_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_0_0 = cert44_layer_5_0_0 := by
  decide

def cert44_seen_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_0_1 = cert44_layer_5_0_1 := by
  decide

def cert44_seen_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_0_2 = cert44_layer_5_0_2 := by
  decide

def cert44_seen_5_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_5_0_3 : List ChainEdge :=
  []

theorem cert44_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_0_3 = cert44_layer_5_0_3 := by
  decide

theorem cert44_component_5_0_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 18 cert44_seen_5_0_0 = cert44_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_0_0 cert44_layer_5_0_0 17 cert44_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 17 cert44_seen_5_0_1 = cert44_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_0_1 cert44_layer_5_0_1 16 cert44_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 16 cert44_seen_5_0_2 = cert44_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_0_2 cert44_layer_5_0_2 15 cert44_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 15 cert44_seen_5_0_3 = cert44_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_0_3 cert44_layer_5_0_3_eq 15

theorem cert44_step_5_0 :
    closedCollarIndexStepBool word fiber44 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_0)
    (by decide) (by decide)
    (by simpa [cert44_move_5_0] using cert44_component_5_0_eq)
    (by decide) (by decide) (by decide)

theorem cert44_row_0 :
    closedCollarParentIndexValid word fiber44 cert44.parents 0 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length]

theorem cert44_row_1 :
    closedCollarParentIndexValid word fiber44 cert44.parents 1 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_1_0, cert44_step_0_1]

theorem cert44_row_2 :
    closedCollarParentIndexValid word fiber44 cert44.parents 2 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_2_0, cert44_step_0_2]

theorem cert44_row_3 :
    closedCollarParentIndexValid word fiber44 cert44.parents 3 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_3_1, cert44_step_1_3]

theorem cert44_row_4 :
    closedCollarParentIndexValid word fiber44 cert44.parents 4 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_4_1, cert44_step_1_4]

theorem cert44_row_5 :
    closedCollarParentIndexValid word fiber44 cert44.parents 5 = true := by
  have cert44_fiber_length : fiber44.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_5_0, cert44_step_0_5]

theorem cert44_rows :
    closedCollarSpineRowsValid word fiber44 cert44.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert44_fiber_length : fiber44.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert44_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert44_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert44_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert44_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert44_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert44_row_5
  · omega

theorem cert44_root :
    closedCollarSpineParentsReachRoot fiber44 cert44 = true := by
  decide

theorem cert44_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert44.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert44 closedStates_eq fiber44_eq cert44_rows cert44_root

theorem cert45_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.r, LColor.r] = [] := by
  decide

theorem cert45_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert45_empty

theorem cert46_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.r, LColor.b] = [] := by
  decide

theorem cert46_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert46_empty

theorem cert47_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.r, LColor.p] = [] := by
  decide

theorem cert47_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert47_empty

theorem cert48_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.b, LColor.r] = [] := by
  decide

theorem cert48_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert48_empty

def fiber49 : List (List TauState) :=
[
  [stateAt 144, stateAt 84]
, [stateAt 145, stateAt 92]
]

theorem fiber49_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.b, LColor.b] = fiber49 := by
  decide

def cert49 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.p, LColor.b, LColor.b],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert49_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert49_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert49_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert49_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert49_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber49 0 [])
      LColor.b LColor.p cert49_seen_0_1_0 = cert49_layer_0_1_0 := by
  decide

def cert49_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert49_layer_0_1_1 : List ChainEdge :=
  []

theorem cert49_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber49 0 [])
      LColor.b LColor.p cert49_seen_0_1_1 = cert49_layer_0_1_1 := by
  decide

theorem cert49_component_0_1_eq :
    closedCollarComponent word (listGetD fiber49 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert49_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber49 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber49 0 [])
      LColor.b LColor.p 18 cert49_seen_0_1_0 = cert49_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber49 0 []) LColor.b LColor.p
    cert49_seen_0_1_0 cert49_layer_0_1_0 17 cert49_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber49 0 [])
      LColor.b LColor.p 17 cert49_seen_0_1_1 = cert49_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber49 0 []) LColor.b LColor.p
    cert49_seen_0_1_1 cert49_layer_0_1_1_eq 17

theorem cert49_step_0_1 :
    closedCollarIndexStepBool word fiber49 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert49_move_0_1)
    (by decide) (by decide)
    (by simpa [cert49_move_0_1] using cert49_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert49_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert49_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert49_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert49_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert49_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber49 1 [])
      LColor.b LColor.p cert49_seen_1_0_0 = cert49_layer_1_0_0 := by
  decide

def cert49_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert49_layer_1_0_1 : List ChainEdge :=
  []

theorem cert49_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber49 1 [])
      LColor.b LColor.p cert49_seen_1_0_1 = cert49_layer_1_0_1 := by
  decide

theorem cert49_component_1_0_eq :
    closedCollarComponent word (listGetD fiber49 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert49_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber49 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber49 1 [])
      LColor.b LColor.p 18 cert49_seen_1_0_0 = cert49_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber49 1 []) LColor.b LColor.p
    cert49_seen_1_0_0 cert49_layer_1_0_0 17 cert49_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber49 1 [])
      LColor.b LColor.p 17 cert49_seen_1_0_1 = cert49_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber49 1 []) LColor.b LColor.p
    cert49_seen_1_0_1 cert49_layer_1_0_1_eq 17

theorem cert49_step_1_0 :
    closedCollarIndexStepBool word fiber49 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert49_move_1_0)
    (by decide) (by decide)
    (by simpa [cert49_move_1_0] using cert49_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert49_row_0 :
    closedCollarParentIndexValid word fiber49 cert49.parents 0 = true := by
  have cert49_fiber_length : fiber49.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert49, listGetD, cert49_fiber_length]

theorem cert49_row_1 :
    closedCollarParentIndexValid word fiber49 cert49.parents 1 = true := by
  have cert49_fiber_length : fiber49.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert49, listGetD, cert49_fiber_length, cert49_step_1_0, cert49_step_0_1]

theorem cert49_rows :
    closedCollarSpineRowsValid word fiber49 cert49.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert49_fiber_length : fiber49.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert49_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert49_row_1
  · omega

theorem cert49_root :
    closedCollarSpineParentsReachRoot fiber49 cert49 = true := by
  decide

theorem cert49_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.b] := by
  change closedCollarFiberKempeConnected word cert49.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert49 closedStates_eq fiber49_eq cert49_rows cert49_root

def fiber50 : List (List TauState) :=
[
  [stateAt 80, stateAt 80]
, [stateAt 81, stateAt 88]
, [stateAt 82, stateAt 16]
, [stateAt 83, stateAt 24]
, [stateAt 102, stateAt 64]
, [stateAt 103, stateAt 72]
]

theorem fiber50_eq :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.b, LColor.p] = fiber50 := by
  decide

def cert50 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.p, LColor.b, LColor.p],
    root := 0,
    maxDepth := 2,
    parents := [0, 0, 0, 1, 1, 0] }

def cert50_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_1_0 = cert50_layer_0_1_0 := by
  decide

def cert50_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_0_1_1 : List ChainEdge :=
  []

theorem cert50_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_1_1 = cert50_layer_0_1_1 := by
  decide

theorem cert50_component_0_1_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 18 cert50_seen_0_1_0 = cert50_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_1_0 cert50_layer_0_1_0 17 cert50_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 17 cert50_seen_0_1_1 = cert50_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_1_1 cert50_layer_0_1_1_eq 17

theorem cert50_step_0_1 :
    closedCollarIndexStepBool word fiber50 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_1)
    (by decide) (by decide)
    (by simpa [cert50_move_0_1] using cert50_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_0 = cert50_layer_0_2_0 := by
  decide

def cert50_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_1 = cert50_layer_0_2_1 := by
  decide

def cert50_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_2 = cert50_layer_0_2_2 := by
  decide

def cert50_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_0_2_3 : List ChainEdge :=
  []

theorem cert50_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_3 = cert50_layer_0_2_3 := by
  decide

theorem cert50_component_0_2_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 18 cert50_seen_0_2_0 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_0 cert50_layer_0_2_0 17 cert50_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 17 cert50_seen_0_2_1 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_1 cert50_layer_0_2_1 16 cert50_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 16 cert50_seen_0_2_2 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_2 cert50_layer_0_2_2 15 cert50_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 15 cert50_seen_0_2_3 = cert50_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_3 cert50_layer_0_2_3_eq 15

theorem cert50_step_0_2 :
    closedCollarIndexStepBool word fiber50 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_2)
    (by decide) (by decide)
    (by simpa [cert50_move_0_2] using cert50_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_0_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_0_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_0 = cert50_layer_0_5_0 := by
  decide

def cert50_seen_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_0_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_1 = cert50_layer_0_5_1 := by
  decide

def cert50_seen_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_0_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_2 = cert50_layer_0_5_2 := by
  decide

def cert50_seen_0_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_0_5_3 : List ChainEdge :=
  []

theorem cert50_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_3 = cert50_layer_0_5_3 := by
  decide

theorem cert50_component_0_5_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 18 cert50_seen_0_5_0 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_0 cert50_layer_0_5_0 17 cert50_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 17 cert50_seen_0_5_1 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_1 cert50_layer_0_5_1 16 cert50_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 16 cert50_seen_0_5_2 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_2 cert50_layer_0_5_2 15 cert50_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 15 cert50_seen_0_5_3 = cert50_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_3 cert50_layer_0_5_3_eq 15

theorem cert50_step_0_5 :
    closedCollarIndexStepBool word fiber50 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_5)
    (by decide) (by decide)
    (by simpa [cert50_move_0_5] using cert50_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_0_0 = cert50_layer_1_0_0 := by
  decide

def cert50_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_1_0_1 : List ChainEdge :=
  []

theorem cert50_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_0_1 = cert50_layer_1_0_1 := by
  decide

theorem cert50_component_1_0_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 18 cert50_seen_1_0_0 = cert50_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_0_0 cert50_layer_1_0_0 17 cert50_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 17 cert50_seen_1_0_1 = cert50_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_0_1 cert50_layer_1_0_1_eq 17

theorem cert50_step_1_0 :
    closedCollarIndexStepBool word fiber50 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_0)
    (by decide) (by decide)
    (by simpa [cert50_move_1_0] using cert50_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_0 = cert50_layer_1_3_0 := by
  decide

def cert50_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_1 = cert50_layer_1_3_1 := by
  decide

def cert50_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_2 = cert50_layer_1_3_2 := by
  decide

def cert50_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_1_3_3 : List ChainEdge :=
  []

theorem cert50_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_3 = cert50_layer_1_3_3 := by
  decide

theorem cert50_component_1_3_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 18 cert50_seen_1_3_0 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_0 cert50_layer_1_3_0 17 cert50_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 17 cert50_seen_1_3_1 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_1 cert50_layer_1_3_1 16 cert50_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 16 cert50_seen_1_3_2 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_2 cert50_layer_1_3_2 15 cert50_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 15 cert50_seen_1_3_3 = cert50_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_3 cert50_layer_1_3_3_eq 15

theorem cert50_step_1_3 :
    closedCollarIndexStepBool word fiber50 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_3)
    (by decide) (by decide)
    (by simpa [cert50_move_1_3] using cert50_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_1_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_0 = cert50_layer_1_4_0 := by
  decide

def cert50_seen_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_1_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_1 = cert50_layer_1_4_1 := by
  decide

def cert50_seen_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_1_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_2 = cert50_layer_1_4_2 := by
  decide

def cert50_seen_1_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_1_4_3 : List ChainEdge :=
  []

theorem cert50_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_3 = cert50_layer_1_4_3 := by
  decide

theorem cert50_component_1_4_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 18 cert50_seen_1_4_0 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_0 cert50_layer_1_4_0 17 cert50_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 17 cert50_seen_1_4_1 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_1 cert50_layer_1_4_1 16 cert50_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 16 cert50_seen_1_4_2 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_2 cert50_layer_1_4_2 15 cert50_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 15 cert50_seen_1_4_3 = cert50_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_3 cert50_layer_1_4_3_eq 15

theorem cert50_step_1_4 :
    closedCollarIndexStepBool word fiber50 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_4)
    (by decide) (by decide)
    (by simpa [cert50_move_1_4] using cert50_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert50_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_0 = cert50_layer_2_0_0 := by
  decide

def cert50_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_1 = cert50_layer_2_0_1 := by
  decide

def cert50_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_2 = cert50_layer_2_0_2 := by
  decide

def cert50_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_2_0_3 : List ChainEdge :=
  []

theorem cert50_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_3 = cert50_layer_2_0_3 := by
  decide

theorem cert50_component_2_0_eq :
    closedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 18 cert50_seen_2_0_0 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_0 cert50_layer_2_0_0 17 cert50_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 17 cert50_seen_2_0_1 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_1 cert50_layer_2_0_1 16 cert50_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 16 cert50_seen_2_0_2 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_2 cert50_layer_2_0_2 15 cert50_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 15 cert50_seen_2_0_3 = cert50_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_3 cert50_layer_2_0_3_eq 15

theorem cert50_step_2_0 :
    closedCollarIndexStepBool word fiber50 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_2_0)
    (by decide) (by decide)
    (by simpa [cert50_move_2_0] using cert50_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_0 = cert50_layer_3_1_0 := by
  decide

def cert50_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_1 = cert50_layer_3_1_1 := by
  decide

def cert50_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_2 = cert50_layer_3_1_2 := by
  decide

def cert50_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_3_1_3 : List ChainEdge :=
  []

theorem cert50_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_3 = cert50_layer_3_1_3 := by
  decide

theorem cert50_component_3_1_eq :
    closedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 18 cert50_seen_3_1_0 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_0 cert50_layer_3_1_0 17 cert50_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 17 cert50_seen_3_1_1 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_1 cert50_layer_3_1_1 16 cert50_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 16 cert50_seen_3_1_2 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_2 cert50_layer_3_1_2 15 cert50_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 15 cert50_seen_3_1_3 = cert50_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_3 cert50_layer_3_1_3_eq 15

theorem cert50_step_3_1 :
    closedCollarIndexStepBool word fiber50 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_3_1)
    (by decide) (by decide)
    (by simpa [cert50_move_3_1] using cert50_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_4_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_0 = cert50_layer_4_1_0 := by
  decide

def cert50_seen_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_4_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_1 = cert50_layer_4_1_1 := by
  decide

def cert50_seen_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_4_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_2 = cert50_layer_4_1_2 := by
  decide

def cert50_seen_4_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_4_1_3 : List ChainEdge :=
  []

theorem cert50_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_3 = cert50_layer_4_1_3 := by
  decide

theorem cert50_component_4_1_eq :
    closedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 18 cert50_seen_4_1_0 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_0 cert50_layer_4_1_0 17 cert50_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 17 cert50_seen_4_1_1 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_1 cert50_layer_4_1_1 16 cert50_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 16 cert50_seen_4_1_2 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_2 cert50_layer_4_1_2 15 cert50_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 15 cert50_seen_4_1_3 = cert50_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_3 cert50_layer_4_1_3_eq 15

theorem cert50_step_4_1 :
    closedCollarIndexStepBool word fiber50 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_4_1)
    (by decide) (by decide)
    (by simpa [cert50_move_4_1] using cert50_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_5_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_0 = cert50_layer_5_0_0 := by
  decide

def cert50_seen_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_5_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_1 = cert50_layer_5_0_1 := by
  decide

def cert50_seen_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_5_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_2 = cert50_layer_5_0_2 := by
  decide

def cert50_seen_5_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_5_0_3 : List ChainEdge :=
  []

theorem cert50_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_3 = cert50_layer_5_0_3 := by
  decide

theorem cert50_component_5_0_eq :
    closedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 18 cert50_seen_5_0_0 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_0 cert50_layer_5_0_0 17 cert50_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 17 cert50_seen_5_0_1 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_1 cert50_layer_5_0_1 16 cert50_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 16 cert50_seen_5_0_2 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_2 cert50_layer_5_0_2 15 cert50_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 15 cert50_seen_5_0_3 = cert50_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_3 cert50_layer_5_0_3_eq 15

theorem cert50_step_5_0 :
    closedCollarIndexStepBool word fiber50 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_5_0)
    (by decide) (by decide)
    (by simpa [cert50_move_5_0] using cert50_component_5_0_eq)
    (by decide) (by decide) (by decide)

theorem cert50_row_0 :
    closedCollarParentIndexValid word fiber50 cert50.parents 0 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length]

theorem cert50_row_1 :
    closedCollarParentIndexValid word fiber50 cert50.parents 1 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_1_0, cert50_step_0_1]

theorem cert50_row_2 :
    closedCollarParentIndexValid word fiber50 cert50.parents 2 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_2_0, cert50_step_0_2]

theorem cert50_row_3 :
    closedCollarParentIndexValid word fiber50 cert50.parents 3 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_3_1, cert50_step_1_3]

theorem cert50_row_4 :
    closedCollarParentIndexValid word fiber50 cert50.parents 4 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_4_1, cert50_step_1_4]

theorem cert50_row_5 :
    closedCollarParentIndexValid word fiber50 cert50.parents 5 = true := by
  have cert50_fiber_length : fiber50.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_5_0, cert50_step_0_5]

theorem cert50_rows :
    closedCollarSpineRowsValid word fiber50 cert50.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert50_fiber_length : fiber50.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert50_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert50_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert50_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert50_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert50_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert50_row_5
  · omega

theorem cert50_root :
    closedCollarSpineParentsReachRoot fiber50 cert50 = true := by
  decide

theorem cert50_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.p] := by
  change closedCollarFiberKempeConnected word cert50.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert50 closedStates_eq fiber50_eq cert50_rows cert50_root

theorem cert51_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.p, LColor.r] = [] := by
  decide

theorem cert51_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert51_empty

theorem cert52_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.p, LColor.b] = [] := by
  decide

theorem cert52_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert52_empty

theorem cert53_empty :
    closedCollarFiberFrom word closedStates [LColor.b, LColor.p, LColor.p, LColor.p] = [] := by
  decide

theorem cert53_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert53_empty

theorem cert54_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.r, LColor.r] = [] := by
  decide

theorem cert54_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert54_empty

theorem cert55_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.r, LColor.b] = [] := by
  decide

theorem cert55_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert55_empty

theorem cert56_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.r, LColor.p] = [] := by
  decide

theorem cert56_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert56_empty

theorem cert57_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.b, LColor.r] = [] := by
  decide

theorem cert57_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert57_empty

theorem cert58_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.b, LColor.b] = [] := by
  decide

theorem cert58_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert58_empty

theorem cert59_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.b, LColor.p] = [] := by
  decide

theorem cert59_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert59_empty

def fiber60 : List (List TauState) :=
[
  [stateAt 140, stateAt 165]
, [stateAt 141, stateAt 173]
, [stateAt 188, stateAt 181]
, [stateAt 189, stateAt 189]
, [stateAt 190, stateAt 117]
, [stateAt 191, stateAt 125]
]

theorem fiber60_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.p, LColor.r] = fiber60 := by
  decide

def cert60 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.r, LColor.p, LColor.r],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 0, 1, 2, 3] }

def cert60_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert60_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert60_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert60_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.b LColor.p cert60_seen_0_1_0 = cert60_layer_0_1_0 := by
  decide

def cert60_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_layer_0_1_1 : List ChainEdge :=
  []

theorem cert60_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.b LColor.p cert60_seen_0_1_1 = cert60_layer_0_1_1 := by
  decide

theorem cert60_component_0_1_eq :
    closedCollarComponent word (listGetD fiber60 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert60_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.b LColor.p 18 cert60_seen_0_1_0 = cert60_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 0 []) LColor.b LColor.p
    cert60_seen_0_1_0 cert60_layer_0_1_0 17 cert60_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.b LColor.p 17 cert60_seen_0_1_1 = cert60_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 0 []) LColor.b LColor.p
    cert60_seen_0_1_1 cert60_layer_0_1_1_eq 17

theorem cert60_step_0_1 :
    closedCollarIndexStepBool word fiber60 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_0_1)
    (by decide) (by decide)
    (by simpa [cert60_move_0_1] using cert60_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert60_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert60_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert60_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert60_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.r LColor.b cert60_seen_0_2_0 = cert60_layer_0_2_0 := by
  decide

def cert60_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert60_layer_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert60_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.r LColor.b cert60_seen_0_2_1 = cert60_layer_0_2_1 := by
  decide

def cert60_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert60_layer_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert60_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.r LColor.b cert60_seen_0_2_2 = cert60_layer_0_2_2 := by
  decide

def cert60_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_layer_0_2_3 : List ChainEdge :=
  []

theorem cert60_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 0 [])
      LColor.r LColor.b cert60_seen_0_2_3 = cert60_layer_0_2_3 := by
  decide

theorem cert60_component_0_2_eq :
    closedCollarComponent word (listGetD fiber60 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert60_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.r LColor.b 18 cert60_seen_0_2_0 = cert60_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 0 []) LColor.r LColor.b
    cert60_seen_0_2_0 cert60_layer_0_2_0 17 cert60_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.r LColor.b 17 cert60_seen_0_2_1 = cert60_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 0 []) LColor.r LColor.b
    cert60_seen_0_2_1 cert60_layer_0_2_1 16 cert60_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.r LColor.b 16 cert60_seen_0_2_2 = cert60_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 0 []) LColor.r LColor.b
    cert60_seen_0_2_2 cert60_layer_0_2_2 15 cert60_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 0 [])
      LColor.r LColor.b 15 cert60_seen_0_2_3 = cert60_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 0 []) LColor.r LColor.b
    cert60_seen_0_2_3 cert60_layer_0_2_3_eq 15

theorem cert60_step_0_2 :
    closedCollarIndexStepBool word fiber60 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_0_2)
    (by decide) (by decide)
    (by simpa [cert60_move_0_2] using cert60_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert60_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert60_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert60_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert60_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.b LColor.p cert60_seen_1_0_0 = cert60_layer_1_0_0 := by
  decide

def cert60_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_layer_1_0_1 : List ChainEdge :=
  []

theorem cert60_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.b LColor.p cert60_seen_1_0_1 = cert60_layer_1_0_1 := by
  decide

theorem cert60_component_1_0_eq :
    closedCollarComponent word (listGetD fiber60 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert60_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.b LColor.p 18 cert60_seen_1_0_0 = cert60_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 1 []) LColor.b LColor.p
    cert60_seen_1_0_0 cert60_layer_1_0_0 17 cert60_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.b LColor.p 17 cert60_seen_1_0_1 = cert60_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 1 []) LColor.b LColor.p
    cert60_seen_1_0_1 cert60_layer_1_0_1_eq 17

theorem cert60_step_1_0 :
    closedCollarIndexStepBool word fiber60 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_1_0)
    (by decide) (by decide)
    (by simpa [cert60_move_1_0] using cert60_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert60_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert60_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert60_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert60_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert60_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.r LColor.b cert60_seen_1_3_0 = cert60_layer_1_3_0 := by
  decide

def cert60_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert60_layer_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert60_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.r LColor.b cert60_seen_1_3_1 = cert60_layer_1_3_1 := by
  decide

def cert60_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert60_layer_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert60_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.r LColor.b cert60_seen_1_3_2 = cert60_layer_1_3_2 := by
  decide

def cert60_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert60_layer_1_3_3 : List ChainEdge :=
  []

theorem cert60_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 1 [])
      LColor.r LColor.b cert60_seen_1_3_3 = cert60_layer_1_3_3 := by
  decide

theorem cert60_component_1_3_eq :
    closedCollarComponent word (listGetD fiber60 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert60_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.r LColor.b 18 cert60_seen_1_3_0 = cert60_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 1 []) LColor.r LColor.b
    cert60_seen_1_3_0 cert60_layer_1_3_0 17 cert60_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.r LColor.b 17 cert60_seen_1_3_1 = cert60_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 1 []) LColor.r LColor.b
    cert60_seen_1_3_1 cert60_layer_1_3_1 16 cert60_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.r LColor.b 16 cert60_seen_1_3_2 = cert60_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 1 []) LColor.r LColor.b
    cert60_seen_1_3_2 cert60_layer_1_3_2 15 cert60_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 1 [])
      LColor.r LColor.b 15 cert60_seen_1_3_3 = cert60_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 1 []) LColor.r LColor.b
    cert60_seen_1_3_3 cert60_layer_1_3_3_eq 15

theorem cert60_step_1_3 :
    closedCollarIndexStepBool word fiber60 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_1_3)
    (by decide) (by decide)
    (by simpa [cert60_move_1_3] using cert60_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert60_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert60_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert60_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert60_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.r LColor.b cert60_seen_2_0_0 = cert60_layer_2_0_0 := by
  decide

def cert60_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert60_layer_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert60_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.r LColor.b cert60_seen_2_0_1 = cert60_layer_2_0_1 := by
  decide

def cert60_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert60_layer_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert60_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.r LColor.b cert60_seen_2_0_2 = cert60_layer_2_0_2 := by
  decide

def cert60_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert60_layer_2_0_3 : List ChainEdge :=
  []

theorem cert60_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.r LColor.b cert60_seen_2_0_3 = cert60_layer_2_0_3 := by
  decide

theorem cert60_component_2_0_eq :
    closedCollarComponent word (listGetD fiber60 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert60_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.r LColor.b 18 cert60_seen_2_0_0 = cert60_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.r LColor.b
    cert60_seen_2_0_0 cert60_layer_2_0_0 17 cert60_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.r LColor.b 17 cert60_seen_2_0_1 = cert60_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.r LColor.b
    cert60_seen_2_0_1 cert60_layer_2_0_1 16 cert60_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.r LColor.b 16 cert60_seen_2_0_2 = cert60_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.r LColor.b
    cert60_seen_2_0_2 cert60_layer_2_0_2 15 cert60_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.r LColor.b 15 cert60_seen_2_0_3 = cert60_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 2 []) LColor.r LColor.b
    cert60_seen_2_0_3 cert60_layer_2_0_3_eq 15

theorem cert60_step_2_0 :
    closedCollarIndexStepBool word fiber60 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_2_0)
    (by decide) (by decide)
    (by simpa [cert60_move_2_0] using cert60_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert60_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert60_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert60_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert60_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.b LColor.p cert60_seen_2_4_0 = cert60_layer_2_4_0 := by
  decide

def cert60_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert60_layer_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert60_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.b LColor.p cert60_seen_2_4_1 = cert60_layer_2_4_1 := by
  decide

def cert60_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert60_layer_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert60_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.b LColor.p cert60_seen_2_4_2 = cert60_layer_2_4_2 := by
  decide

def cert60_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_layer_2_4_3 : List ChainEdge :=
  []

theorem cert60_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 2 [])
      LColor.b LColor.p cert60_seen_2_4_3 = cert60_layer_2_4_3 := by
  decide

theorem cert60_component_2_4_eq :
    closedCollarComponent word (listGetD fiber60 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert60_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.b LColor.p 18 cert60_seen_2_4_0 = cert60_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.b LColor.p
    cert60_seen_2_4_0 cert60_layer_2_4_0 17 cert60_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.b LColor.p 17 cert60_seen_2_4_1 = cert60_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.b LColor.p
    cert60_seen_2_4_1 cert60_layer_2_4_1 16 cert60_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.b LColor.p 16 cert60_seen_2_4_2 = cert60_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 2 []) LColor.b LColor.p
    cert60_seen_2_4_2 cert60_layer_2_4_2 15 cert60_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 2 [])
      LColor.b LColor.p 15 cert60_seen_2_4_3 = cert60_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 2 []) LColor.b LColor.p
    cert60_seen_2_4_3 cert60_layer_2_4_3_eq 15

theorem cert60_step_2_4 :
    closedCollarIndexStepBool word fiber60 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_2_4)
    (by decide) (by decide)
    (by simpa [cert60_move_2_4] using cert60_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert60_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert60_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert60_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert60_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert60_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.r LColor.b cert60_seen_3_1_0 = cert60_layer_3_1_0 := by
  decide

def cert60_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert60_layer_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert60_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.r LColor.b cert60_seen_3_1_1 = cert60_layer_3_1_1 := by
  decide

def cert60_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert60_layer_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert60_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.r LColor.b cert60_seen_3_1_2 = cert60_layer_3_1_2 := by
  decide

def cert60_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert60_layer_3_1_3 : List ChainEdge :=
  []

theorem cert60_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.r LColor.b cert60_seen_3_1_3 = cert60_layer_3_1_3 := by
  decide

theorem cert60_component_3_1_eq :
    closedCollarComponent word (listGetD fiber60 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert60_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.r LColor.b 18 cert60_seen_3_1_0 = cert60_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.r LColor.b
    cert60_seen_3_1_0 cert60_layer_3_1_0 17 cert60_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.r LColor.b 17 cert60_seen_3_1_1 = cert60_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.r LColor.b
    cert60_seen_3_1_1 cert60_layer_3_1_1 16 cert60_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.r LColor.b 16 cert60_seen_3_1_2 = cert60_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.r LColor.b
    cert60_seen_3_1_2 cert60_layer_3_1_2 15 cert60_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.r LColor.b 15 cert60_seen_3_1_3 = cert60_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 3 []) LColor.r LColor.b
    cert60_seen_3_1_3 cert60_layer_3_1_3_eq 15

theorem cert60_step_3_1 :
    closedCollarIndexStepBool word fiber60 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_3_1)
    (by decide) (by decide)
    (by simpa [cert60_move_3_1] using cert60_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert60_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert60_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert60_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert60_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.b LColor.p cert60_seen_3_5_0 = cert60_layer_3_5_0 := by
  decide

def cert60_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert60_layer_3_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert60_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.b LColor.p cert60_seen_3_5_1 = cert60_layer_3_5_1 := by
  decide

def cert60_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert60_layer_3_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert60_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.b LColor.p cert60_seen_3_5_2 = cert60_layer_3_5_2 := by
  decide

def cert60_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_layer_3_5_3 : List ChainEdge :=
  []

theorem cert60_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 3 [])
      LColor.b LColor.p cert60_seen_3_5_3 = cert60_layer_3_5_3 := by
  decide

theorem cert60_component_3_5_eq :
    closedCollarComponent word (listGetD fiber60 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert60_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.b LColor.p 18 cert60_seen_3_5_0 = cert60_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.b LColor.p
    cert60_seen_3_5_0 cert60_layer_3_5_0 17 cert60_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.b LColor.p 17 cert60_seen_3_5_1 = cert60_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.b LColor.p
    cert60_seen_3_5_1 cert60_layer_3_5_1 16 cert60_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.b LColor.p 16 cert60_seen_3_5_2 = cert60_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 3 []) LColor.b LColor.p
    cert60_seen_3_5_2 cert60_layer_3_5_2 15 cert60_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 3 [])
      LColor.b LColor.p 15 cert60_seen_3_5_3 = cert60_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 3 []) LColor.b LColor.p
    cert60_seen_3_5_3 cert60_layer_3_5_3_eq 15

theorem cert60_step_3_5 :
    closedCollarIndexStepBool word fiber60 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_3_5)
    (by decide) (by decide)
    (by simpa [cert60_move_3_5] using cert60_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert60_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert60_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert60_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert60_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 4 [])
      LColor.b LColor.p cert60_seen_4_2_0 = cert60_layer_4_2_0 := by
  decide

def cert60_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert60_layer_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert60_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 4 [])
      LColor.b LColor.p cert60_seen_4_2_1 = cert60_layer_4_2_1 := by
  decide

def cert60_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert60_layer_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert60_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 4 [])
      LColor.b LColor.p cert60_seen_4_2_2 = cert60_layer_4_2_2 := by
  decide

def cert60_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_layer_4_2_3 : List ChainEdge :=
  []

theorem cert60_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 4 [])
      LColor.b LColor.p cert60_seen_4_2_3 = cert60_layer_4_2_3 := by
  decide

theorem cert60_component_4_2_eq :
    closedCollarComponent word (listGetD fiber60 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert60_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 4 [])
      LColor.b LColor.p 18 cert60_seen_4_2_0 = cert60_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 4 []) LColor.b LColor.p
    cert60_seen_4_2_0 cert60_layer_4_2_0 17 cert60_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 4 [])
      LColor.b LColor.p 17 cert60_seen_4_2_1 = cert60_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 4 []) LColor.b LColor.p
    cert60_seen_4_2_1 cert60_layer_4_2_1 16 cert60_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 4 [])
      LColor.b LColor.p 16 cert60_seen_4_2_2 = cert60_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 4 []) LColor.b LColor.p
    cert60_seen_4_2_2 cert60_layer_4_2_2 15 cert60_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 4 [])
      LColor.b LColor.p 15 cert60_seen_4_2_3 = cert60_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 4 []) LColor.b LColor.p
    cert60_seen_4_2_3 cert60_layer_4_2_3_eq 15

theorem cert60_step_4_2 :
    closedCollarIndexStepBool word fiber60 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_4_2)
    (by decide) (by decide)
    (by simpa [cert60_move_4_2] using cert60_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert60_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert60_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert60_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert60_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber60 5 [])
      LColor.b LColor.p cert60_seen_5_3_0 = cert60_layer_5_3_0 := by
  decide

def cert60_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert60_layer_5_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert60_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber60 5 [])
      LColor.b LColor.p cert60_seen_5_3_1 = cert60_layer_5_3_1 := by
  decide

def cert60_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert60_layer_5_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert60_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber60 5 [])
      LColor.b LColor.p cert60_seen_5_3_2 = cert60_layer_5_3_2 := by
  decide

def cert60_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert60_layer_5_3_3 : List ChainEdge :=
  []

theorem cert60_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber60 5 [])
      LColor.b LColor.p cert60_seen_5_3_3 = cert60_layer_5_3_3 := by
  decide

theorem cert60_component_5_3_eq :
    closedCollarComponent word (listGetD fiber60 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert60_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber60 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber60 5 [])
      LColor.b LColor.p 18 cert60_seen_5_3_0 = cert60_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 5 []) LColor.b LColor.p
    cert60_seen_5_3_0 cert60_layer_5_3_0 17 cert60_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber60 5 [])
      LColor.b LColor.p 17 cert60_seen_5_3_1 = cert60_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 5 []) LColor.b LColor.p
    cert60_seen_5_3_1 cert60_layer_5_3_1 16 cert60_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber60 5 [])
      LColor.b LColor.p 16 cert60_seen_5_3_2 = cert60_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber60 5 []) LColor.b LColor.p
    cert60_seen_5_3_2 cert60_layer_5_3_2 15 cert60_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber60 5 [])
      LColor.b LColor.p 15 cert60_seen_5_3_3 = cert60_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber60 5 []) LColor.b LColor.p
    cert60_seen_5_3_3 cert60_layer_5_3_3_eq 15

theorem cert60_step_5_3 :
    closedCollarIndexStepBool word fiber60 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert60_move_5_3)
    (by decide) (by decide)
    (by simpa [cert60_move_5_3] using cert60_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert60_row_0 :
    closedCollarParentIndexValid word fiber60 cert60.parents 0 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length]

theorem cert60_row_1 :
    closedCollarParentIndexValid word fiber60 cert60.parents 1 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length, cert60_step_1_0, cert60_step_0_1]

theorem cert60_row_2 :
    closedCollarParentIndexValid word fiber60 cert60.parents 2 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length, cert60_step_2_0, cert60_step_0_2]

theorem cert60_row_3 :
    closedCollarParentIndexValid word fiber60 cert60.parents 3 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length, cert60_step_3_1, cert60_step_1_3]

theorem cert60_row_4 :
    closedCollarParentIndexValid word fiber60 cert60.parents 4 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length, cert60_step_4_2, cert60_step_2_4]

theorem cert60_row_5 :
    closedCollarParentIndexValid word fiber60 cert60.parents 5 = true := by
  have cert60_fiber_length : fiber60.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert60, listGetD, cert60_fiber_length, cert60_step_5_3, cert60_step_3_5]

theorem cert60_rows :
    closedCollarSpineRowsValid word fiber60 cert60.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert60_fiber_length : fiber60.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert60_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert60_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert60_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert60_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert60_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert60_row_5
  · omega

theorem cert60_root :
    closedCollarSpineParentsReachRoot fiber60 cert60 = true := by
  decide

theorem cert60_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.p, LColor.r] := by
  change closedCollarFiberKempeConnected word cert60.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert60 closedStates_eq fiber60_eq cert60_rows cert60_root

theorem cert61_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.p, LColor.b] = [] := by
  decide

theorem cert61_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert61_empty

def fiber62 : List (List TauState) :=
[
  [stateAt 30, stateAt 177]
, [stateAt 31, stateAt 185]
]

theorem fiber62_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.r, LColor.p, LColor.p] = fiber62 := by
  decide

def cert62 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.r, LColor.p, LColor.p],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert62_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert62_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert62_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert62_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert62_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber62 0 [])
      LColor.r LColor.p cert62_seen_0_1_0 = cert62_layer_0_1_0 := by
  decide

def cert62_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert62_layer_0_1_1 : List ChainEdge :=
  []

theorem cert62_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber62 0 [])
      LColor.r LColor.p cert62_seen_0_1_1 = cert62_layer_0_1_1 := by
  decide

theorem cert62_component_0_1_eq :
    closedCollarComponent word (listGetD fiber62 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert62_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber62 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber62 0 [])
      LColor.r LColor.p 18 cert62_seen_0_1_0 = cert62_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber62 0 []) LColor.r LColor.p
    cert62_seen_0_1_0 cert62_layer_0_1_0 17 cert62_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber62 0 [])
      LColor.r LColor.p 17 cert62_seen_0_1_1 = cert62_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber62 0 []) LColor.r LColor.p
    cert62_seen_0_1_1 cert62_layer_0_1_1_eq 17

theorem cert62_step_0_1 :
    closedCollarIndexStepBool word fiber62 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert62_move_0_1)
    (by decide) (by decide)
    (by simpa [cert62_move_0_1] using cert62_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert62_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert62_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert62_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert62_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert62_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber62 1 [])
      LColor.r LColor.p cert62_seen_1_0_0 = cert62_layer_1_0_0 := by
  decide

def cert62_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert62_layer_1_0_1 : List ChainEdge :=
  []

theorem cert62_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber62 1 [])
      LColor.r LColor.p cert62_seen_1_0_1 = cert62_layer_1_0_1 := by
  decide

theorem cert62_component_1_0_eq :
    closedCollarComponent word (listGetD fiber62 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert62_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber62 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber62 1 [])
      LColor.r LColor.p 18 cert62_seen_1_0_0 = cert62_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber62 1 []) LColor.r LColor.p
    cert62_seen_1_0_0 cert62_layer_1_0_0 17 cert62_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber62 1 [])
      LColor.r LColor.p 17 cert62_seen_1_0_1 = cert62_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber62 1 []) LColor.r LColor.p
    cert62_seen_1_0_1 cert62_layer_1_0_1_eq 17

theorem cert62_step_1_0 :
    closedCollarIndexStepBool word fiber62 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert62_move_1_0)
    (by decide) (by decide)
    (by simpa [cert62_move_1_0] using cert62_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert62_row_0 :
    closedCollarParentIndexValid word fiber62 cert62.parents 0 = true := by
  have cert62_fiber_length : fiber62.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert62, listGetD, cert62_fiber_length]

theorem cert62_row_1 :
    closedCollarParentIndexValid word fiber62 cert62.parents 1 = true := by
  have cert62_fiber_length : fiber62.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert62, listGetD, cert62_fiber_length, cert62_step_1_0, cert62_step_0_1]

theorem cert62_rows :
    closedCollarSpineRowsValid word fiber62 cert62.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert62_fiber_length : fiber62.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert62_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert62_row_1
  · omega

theorem cert62_root :
    closedCollarSpineParentsReachRoot fiber62 cert62 = true := by
  decide

theorem cert62_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert62.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert62 closedStates_eq fiber62_eq cert62_rows cert62_root

theorem cert63_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.r, LColor.r] = [] := by
  decide

theorem cert63_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert63_empty

theorem cert64_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.r, LColor.b] = [] := by
  decide

theorem cert64_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert64_empty

theorem cert65_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.r, LColor.p] = [] := by
  decide

theorem cert65_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert65_empty

theorem cert66_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.b, LColor.r] = [] := by
  decide

theorem cert66_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert66_empty

theorem cert67_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.b, LColor.b] = [] := by
  decide

theorem cert67_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert67_empty

theorem cert68_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.b, LColor.p] = [] := by
  decide

theorem cert68_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert68_empty

theorem cert69_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.p, LColor.r] = [] := by
  decide

theorem cert69_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert69_empty

def fiber70 : List (List TauState) :=
[
  [stateAt 156, stateAt 149]
, [stateAt 157, stateAt 157]
, [stateAt 158, stateAt 49]
, [stateAt 159, stateAt 57]
, [stateAt 172, stateAt 133]
, [stateAt 173, stateAt 141]
]

theorem fiber70_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.p, LColor.b] = fiber70 := by
  decide

def cert70 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.b, LColor.p, LColor.b],
    root := 0,
    maxDepth := 2,
    parents := [0, 0, 1, 0, 0, 1] }

def cert70_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert70_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert70_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert70_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.b LColor.p cert70_seen_0_1_0 = cert70_layer_0_1_0 := by
  decide

def cert70_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_layer_0_1_1 : List ChainEdge :=
  []

theorem cert70_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.b LColor.p cert70_seen_0_1_1 = cert70_layer_0_1_1 := by
  decide

theorem cert70_component_0_1_eq :
    closedCollarComponent word (listGetD fiber70 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert70_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.b LColor.p 18 cert70_seen_0_1_0 = cert70_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.b LColor.p
    cert70_seen_0_1_0 cert70_layer_0_1_0 17 cert70_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.b LColor.p 17 cert70_seen_0_1_1 = cert70_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 0 []) LColor.b LColor.p
    cert70_seen_0_1_1 cert70_layer_0_1_1_eq 17

theorem cert70_step_0_1 :
    closedCollarIndexStepBool word fiber70 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_0_1)
    (by decide) (by decide)
    (by simpa [cert70_move_0_1] using cert70_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert70_move_0_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert70_component_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_seen_0_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert70_layer_0_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert70_layer_0_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.p cert70_seen_0_3_0 = cert70_layer_0_3_0 := by
  decide

def cert70_seen_0_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert70_layer_0_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert70_layer_0_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.p cert70_seen_0_3_1 = cert70_layer_0_3_1 := by
  decide

def cert70_seen_0_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert70_layer_0_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert70_layer_0_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.p cert70_seen_0_3_2 = cert70_layer_0_3_2 := by
  decide

def cert70_seen_0_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_layer_0_3_3 : List ChainEdge :=
  []

theorem cert70_layer_0_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.p cert70_seen_0_3_3 = cert70_layer_0_3_3 := by
  decide

theorem cert70_component_0_3_eq :
    closedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert70_component_0_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.p 18 cert70_seen_0_3_0 = cert70_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.p
    cert70_seen_0_3_0 cert70_layer_0_3_0 17 cert70_layer_0_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.p 17 cert70_seen_0_3_1 = cert70_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.p
    cert70_seen_0_3_1 cert70_layer_0_3_1 16 cert70_layer_0_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.p 16 cert70_seen_0_3_2 = cert70_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.p
    cert70_seen_0_3_2 cert70_layer_0_3_2 15 cert70_layer_0_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.p 15 cert70_seen_0_3_3 = cert70_component_0_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 0 []) LColor.r LColor.p
    cert70_seen_0_3_3 cert70_layer_0_3_3_eq 15

theorem cert70_step_0_3 :
    closedCollarIndexStepBool word fiber70 0 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_0_3)
    (by decide) (by decide)
    (by simpa [cert70_move_0_3] using cert70_component_0_3_eq)
    (by decide) (by decide) (by decide)

def cert70_move_0_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert70_component_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_seen_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert70_layer_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert70_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.b cert70_seen_0_4_0 = cert70_layer_0_4_0 := by
  decide

def cert70_seen_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert70_layer_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert70_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.b cert70_seen_0_4_1 = cert70_layer_0_4_1 := by
  decide

def cert70_seen_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert70_layer_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert70_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.b cert70_seen_0_4_2 = cert70_layer_0_4_2 := by
  decide

def cert70_seen_0_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_layer_0_4_3 : List ChainEdge :=
  []

theorem cert70_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 0 [])
      LColor.r LColor.b cert70_seen_0_4_3 = cert70_layer_0_4_3 := by
  decide

theorem cert70_component_0_4_eq :
    closedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert70_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.b 18 cert70_seen_0_4_0 = cert70_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.b
    cert70_seen_0_4_0 cert70_layer_0_4_0 17 cert70_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.b 17 cert70_seen_0_4_1 = cert70_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.b
    cert70_seen_0_4_1 cert70_layer_0_4_1 16 cert70_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.b 16 cert70_seen_0_4_2 = cert70_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 0 []) LColor.r LColor.b
    cert70_seen_0_4_2 cert70_layer_0_4_2 15 cert70_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 0 [])
      LColor.r LColor.b 15 cert70_seen_0_4_3 = cert70_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 0 []) LColor.r LColor.b
    cert70_seen_0_4_3 cert70_layer_0_4_3_eq 15

theorem cert70_step_0_4 :
    closedCollarIndexStepBool word fiber70 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_0_4)
    (by decide) (by decide)
    (by simpa [cert70_move_0_4] using cert70_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert70_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert70_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert70_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert70_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.b LColor.p cert70_seen_1_0_0 = cert70_layer_1_0_0 := by
  decide

def cert70_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_layer_1_0_1 : List ChainEdge :=
  []

theorem cert70_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.b LColor.p cert70_seen_1_0_1 = cert70_layer_1_0_1 := by
  decide

theorem cert70_component_1_0_eq :
    closedCollarComponent word (listGetD fiber70 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert70_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.b LColor.p 18 cert70_seen_1_0_0 = cert70_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.b LColor.p
    cert70_seen_1_0_0 cert70_layer_1_0_0 17 cert70_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.b LColor.p 17 cert70_seen_1_0_1 = cert70_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 1 []) LColor.b LColor.p
    cert70_seen_1_0_1 cert70_layer_1_0_1_eq 17

theorem cert70_step_1_0 :
    closedCollarIndexStepBool word fiber70 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_1_0)
    (by decide) (by decide)
    (by simpa [cert70_move_1_0] using cert70_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert70_move_1_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert70_component_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_seen_1_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert70_layer_1_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert70_layer_1_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.p cert70_seen_1_2_0 = cert70_layer_1_2_0 := by
  decide

def cert70_seen_1_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert70_layer_1_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert70_layer_1_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.p cert70_seen_1_2_1 = cert70_layer_1_2_1 := by
  decide

def cert70_seen_1_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert70_layer_1_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert70_layer_1_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.p cert70_seen_1_2_2 = cert70_layer_1_2_2 := by
  decide

def cert70_seen_1_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_layer_1_2_3 : List ChainEdge :=
  []

theorem cert70_layer_1_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.p cert70_seen_1_2_3 = cert70_layer_1_2_3 := by
  decide

theorem cert70_component_1_2_eq :
    closedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert70_component_1_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.p 18 cert70_seen_1_2_0 = cert70_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.p
    cert70_seen_1_2_0 cert70_layer_1_2_0 17 cert70_layer_1_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.p 17 cert70_seen_1_2_1 = cert70_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.p
    cert70_seen_1_2_1 cert70_layer_1_2_1 16 cert70_layer_1_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.p 16 cert70_seen_1_2_2 = cert70_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.p
    cert70_seen_1_2_2 cert70_layer_1_2_2 15 cert70_layer_1_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.p 15 cert70_seen_1_2_3 = cert70_component_1_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 1 []) LColor.r LColor.p
    cert70_seen_1_2_3 cert70_layer_1_2_3_eq 15

theorem cert70_step_1_2 :
    closedCollarIndexStepBool word fiber70 1 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_1_2)
    (by decide) (by decide)
    (by simpa [cert70_move_1_2] using cert70_component_1_2_eq)
    (by decide) (by decide) (by decide)

def cert70_move_1_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert70_component_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert70_seen_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert70_layer_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert70_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.b cert70_seen_1_5_0 = cert70_layer_1_5_0 := by
  decide

def cert70_seen_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert70_layer_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert70_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.b cert70_seen_1_5_1 = cert70_layer_1_5_1 := by
  decide

def cert70_seen_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert70_layer_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert70_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.b cert70_seen_1_5_2 = cert70_layer_1_5_2 := by
  decide

def cert70_seen_1_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert70_layer_1_5_3 : List ChainEdge :=
  []

theorem cert70_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 1 [])
      LColor.r LColor.b cert70_seen_1_5_3 = cert70_layer_1_5_3 := by
  decide

theorem cert70_component_1_5_eq :
    closedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert70_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.b 18 cert70_seen_1_5_0 = cert70_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.b
    cert70_seen_1_5_0 cert70_layer_1_5_0 17 cert70_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.b 17 cert70_seen_1_5_1 = cert70_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.b
    cert70_seen_1_5_1 cert70_layer_1_5_1 16 cert70_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.b 16 cert70_seen_1_5_2 = cert70_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 1 []) LColor.r LColor.b
    cert70_seen_1_5_2 cert70_layer_1_5_2 15 cert70_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 1 [])
      LColor.r LColor.b 15 cert70_seen_1_5_3 = cert70_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 1 []) LColor.r LColor.b
    cert70_seen_1_5_3 cert70_layer_1_5_3_eq 15

theorem cert70_step_1_5 :
    closedCollarIndexStepBool word fiber70 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_1_5)
    (by decide) (by decide)
    (by simpa [cert70_move_1_5] using cert70_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert70_move_2_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert70_component_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_seen_2_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert70_layer_2_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert70_layer_2_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 2 [])
      LColor.r LColor.p cert70_seen_2_1_0 = cert70_layer_2_1_0 := by
  decide

def cert70_seen_2_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert70_layer_2_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert70_layer_2_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 2 [])
      LColor.r LColor.p cert70_seen_2_1_1 = cert70_layer_2_1_1 := by
  decide

def cert70_seen_2_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert70_layer_2_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert70_layer_2_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 2 [])
      LColor.r LColor.p cert70_seen_2_1_2 = cert70_layer_2_1_2 := by
  decide

def cert70_seen_2_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_layer_2_1_3 : List ChainEdge :=
  []

theorem cert70_layer_2_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 2 [])
      LColor.r LColor.p cert70_seen_2_1_3 = cert70_layer_2_1_3 := by
  decide

theorem cert70_component_2_1_eq :
    closedCollarComponent word (listGetD fiber70 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert70_component_2_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 2 [])
      LColor.r LColor.p 18 cert70_seen_2_1_0 = cert70_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 2 []) LColor.r LColor.p
    cert70_seen_2_1_0 cert70_layer_2_1_0 17 cert70_layer_2_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 2 [])
      LColor.r LColor.p 17 cert70_seen_2_1_1 = cert70_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 2 []) LColor.r LColor.p
    cert70_seen_2_1_1 cert70_layer_2_1_1 16 cert70_layer_2_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 2 [])
      LColor.r LColor.p 16 cert70_seen_2_1_2 = cert70_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 2 []) LColor.r LColor.p
    cert70_seen_2_1_2 cert70_layer_2_1_2 15 cert70_layer_2_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 2 [])
      LColor.r LColor.p 15 cert70_seen_2_1_3 = cert70_component_2_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 2 []) LColor.r LColor.p
    cert70_seen_2_1_3 cert70_layer_2_1_3_eq 15

theorem cert70_step_2_1 :
    closedCollarIndexStepBool word fiber70 2 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_2_1)
    (by decide) (by decide)
    (by simpa [cert70_move_2_1] using cert70_component_2_1_eq)
    (by decide) (by decide) (by decide)

def cert70_move_3_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert70_component_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_seen_3_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert70_layer_3_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert70_layer_3_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 3 [])
      LColor.r LColor.p cert70_seen_3_0_0 = cert70_layer_3_0_0 := by
  decide

def cert70_seen_3_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert70_layer_3_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert70_layer_3_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 3 [])
      LColor.r LColor.p cert70_seen_3_0_1 = cert70_layer_3_0_1 := by
  decide

def cert70_seen_3_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert70_layer_3_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert70_layer_3_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 3 [])
      LColor.r LColor.p cert70_seen_3_0_2 = cert70_layer_3_0_2 := by
  decide

def cert70_seen_3_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert70_layer_3_0_3 : List ChainEdge :=
  []

theorem cert70_layer_3_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 3 [])
      LColor.r LColor.p cert70_seen_3_0_3 = cert70_layer_3_0_3 := by
  decide

theorem cert70_component_3_0_eq :
    closedCollarComponent word (listGetD fiber70 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert70_component_3_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 3 [])
      LColor.r LColor.p 18 cert70_seen_3_0_0 = cert70_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 3 []) LColor.r LColor.p
    cert70_seen_3_0_0 cert70_layer_3_0_0 17 cert70_layer_3_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 3 [])
      LColor.r LColor.p 17 cert70_seen_3_0_1 = cert70_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 3 []) LColor.r LColor.p
    cert70_seen_3_0_1 cert70_layer_3_0_1 16 cert70_layer_3_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 3 [])
      LColor.r LColor.p 16 cert70_seen_3_0_2 = cert70_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 3 []) LColor.r LColor.p
    cert70_seen_3_0_2 cert70_layer_3_0_2 15 cert70_layer_3_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 3 [])
      LColor.r LColor.p 15 cert70_seen_3_0_3 = cert70_component_3_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 3 []) LColor.r LColor.p
    cert70_seen_3_0_3 cert70_layer_3_0_3_eq 15

theorem cert70_step_3_0 :
    closedCollarIndexStepBool word fiber70 3 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_3_0)
    (by decide) (by decide)
    (by simpa [cert70_move_3_0] using cert70_component_3_0_eq)
    (by decide) (by decide) (by decide)

def cert70_move_4_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert70_component_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_seen_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert70_layer_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert70_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 4 [])
      LColor.r LColor.b cert70_seen_4_0_0 = cert70_layer_4_0_0 := by
  decide

def cert70_seen_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert70_layer_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert70_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 4 [])
      LColor.r LColor.b cert70_seen_4_0_1 = cert70_layer_4_0_1 := by
  decide

def cert70_seen_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert70_layer_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert70_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 4 [])
      LColor.r LColor.b cert70_seen_4_0_2 = cert70_layer_4_0_2 := by
  decide

def cert70_seen_4_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert70_layer_4_0_3 : List ChainEdge :=
  []

theorem cert70_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 4 [])
      LColor.r LColor.b cert70_seen_4_0_3 = cert70_layer_4_0_3 := by
  decide

theorem cert70_component_4_0_eq :
    closedCollarComponent word (listGetD fiber70 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert70_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 4 [])
      LColor.r LColor.b 18 cert70_seen_4_0_0 = cert70_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 4 []) LColor.r LColor.b
    cert70_seen_4_0_0 cert70_layer_4_0_0 17 cert70_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 4 [])
      LColor.r LColor.b 17 cert70_seen_4_0_1 = cert70_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 4 []) LColor.r LColor.b
    cert70_seen_4_0_1 cert70_layer_4_0_1 16 cert70_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 4 [])
      LColor.r LColor.b 16 cert70_seen_4_0_2 = cert70_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 4 []) LColor.r LColor.b
    cert70_seen_4_0_2 cert70_layer_4_0_2 15 cert70_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 4 [])
      LColor.r LColor.b 15 cert70_seen_4_0_3 = cert70_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 4 []) LColor.r LColor.b
    cert70_seen_4_0_3 cert70_layer_4_0_3_eq 15

theorem cert70_step_4_0 :
    closedCollarIndexStepBool word fiber70 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_4_0)
    (by decide) (by decide)
    (by simpa [cert70_move_4_0] using cert70_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert70_move_5_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert70_component_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert70_seen_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert70_layer_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert70_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber70 5 [])
      LColor.r LColor.b cert70_seen_5_1_0 = cert70_layer_5_1_0 := by
  decide

def cert70_seen_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert70_layer_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert70_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber70 5 [])
      LColor.r LColor.b cert70_seen_5_1_1 = cert70_layer_5_1_1 := by
  decide

def cert70_seen_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert70_layer_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert70_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber70 5 [])
      LColor.r LColor.b cert70_seen_5_1_2 = cert70_layer_5_1_2 := by
  decide

def cert70_seen_5_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert70_layer_5_1_3 : List ChainEdge :=
  []

theorem cert70_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber70 5 [])
      LColor.r LColor.b cert70_seen_5_1_3 = cert70_layer_5_1_3 := by
  decide

theorem cert70_component_5_1_eq :
    closedCollarComponent word (listGetD fiber70 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert70_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber70 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber70 5 [])
      LColor.r LColor.b 18 cert70_seen_5_1_0 = cert70_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 5 []) LColor.r LColor.b
    cert70_seen_5_1_0 cert70_layer_5_1_0 17 cert70_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber70 5 [])
      LColor.r LColor.b 17 cert70_seen_5_1_1 = cert70_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 5 []) LColor.r LColor.b
    cert70_seen_5_1_1 cert70_layer_5_1_1 16 cert70_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber70 5 [])
      LColor.r LColor.b 16 cert70_seen_5_1_2 = cert70_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber70 5 []) LColor.r LColor.b
    cert70_seen_5_1_2 cert70_layer_5_1_2 15 cert70_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber70 5 [])
      LColor.r LColor.b 15 cert70_seen_5_1_3 = cert70_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber70 5 []) LColor.r LColor.b
    cert70_seen_5_1_3 cert70_layer_5_1_3_eq 15

theorem cert70_step_5_1 :
    closedCollarIndexStepBool word fiber70 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert70_move_5_1)
    (by decide) (by decide)
    (by simpa [cert70_move_5_1] using cert70_component_5_1_eq)
    (by decide) (by decide) (by decide)

theorem cert70_row_0 :
    closedCollarParentIndexValid word fiber70 cert70.parents 0 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length]

theorem cert70_row_1 :
    closedCollarParentIndexValid word fiber70 cert70.parents 1 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length, cert70_step_1_0, cert70_step_0_1]

theorem cert70_row_2 :
    closedCollarParentIndexValid word fiber70 cert70.parents 2 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length, cert70_step_2_1, cert70_step_1_2]

theorem cert70_row_3 :
    closedCollarParentIndexValid word fiber70 cert70.parents 3 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length, cert70_step_3_0, cert70_step_0_3]

theorem cert70_row_4 :
    closedCollarParentIndexValid word fiber70 cert70.parents 4 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length, cert70_step_4_0, cert70_step_0_4]

theorem cert70_row_5 :
    closedCollarParentIndexValid word fiber70 cert70.parents 5 = true := by
  have cert70_fiber_length : fiber70.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert70, listGetD, cert70_fiber_length, cert70_step_5_1, cert70_step_1_5]

theorem cert70_rows :
    closedCollarSpineRowsValid word fiber70 cert70.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert70_fiber_length : fiber70.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert70_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert70_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert70_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert70_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert70_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert70_row_5
  · omega

theorem cert70_root :
    closedCollarSpineParentsReachRoot fiber70 cert70 = true := by
  decide

theorem cert70_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.p, LColor.b] := by
  change closedCollarFiberKempeConnected word cert70.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert70 closedStates_eq fiber70_eq cert70_rows cert70_root

def fiber71 : List (List TauState) :=
[
  [stateAt 92, stateAt 145]
, [stateAt 93, stateAt 153]
]

theorem fiber71_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.b, LColor.p, LColor.p] = fiber71 := by
  decide

def cert71 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.b, LColor.p, LColor.p],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert71_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert71_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert71_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert71_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert71_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber71 0 [])
      LColor.b LColor.p cert71_seen_0_1_0 = cert71_layer_0_1_0 := by
  decide

def cert71_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert71_layer_0_1_1 : List ChainEdge :=
  []

theorem cert71_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber71 0 [])
      LColor.b LColor.p cert71_seen_0_1_1 = cert71_layer_0_1_1 := by
  decide

theorem cert71_component_0_1_eq :
    closedCollarComponent word (listGetD fiber71 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert71_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber71 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber71 0 [])
      LColor.b LColor.p 18 cert71_seen_0_1_0 = cert71_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber71 0 []) LColor.b LColor.p
    cert71_seen_0_1_0 cert71_layer_0_1_0 17 cert71_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber71 0 [])
      LColor.b LColor.p 17 cert71_seen_0_1_1 = cert71_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber71 0 []) LColor.b LColor.p
    cert71_seen_0_1_1 cert71_layer_0_1_1_eq 17

theorem cert71_step_0_1 :
    closedCollarIndexStepBool word fiber71 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert71_move_0_1)
    (by decide) (by decide)
    (by simpa [cert71_move_0_1] using cert71_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert71_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert71_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert71_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert71_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert71_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber71 1 [])
      LColor.b LColor.p cert71_seen_1_0_0 = cert71_layer_1_0_0 := by
  decide

def cert71_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert71_layer_1_0_1 : List ChainEdge :=
  []

theorem cert71_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber71 1 [])
      LColor.b LColor.p cert71_seen_1_0_1 = cert71_layer_1_0_1 := by
  decide

theorem cert71_component_1_0_eq :
    closedCollarComponent word (listGetD fiber71 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert71_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber71 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber71 1 [])
      LColor.b LColor.p 18 cert71_seen_1_0_0 = cert71_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber71 1 []) LColor.b LColor.p
    cert71_seen_1_0_0 cert71_layer_1_0_0 17 cert71_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber71 1 [])
      LColor.b LColor.p 17 cert71_seen_1_0_1 = cert71_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber71 1 []) LColor.b LColor.p
    cert71_seen_1_0_1 cert71_layer_1_0_1_eq 17

theorem cert71_step_1_0 :
    closedCollarIndexStepBool word fiber71 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert71_move_1_0)
    (by decide) (by decide)
    (by simpa [cert71_move_1_0] using cert71_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert71_row_0 :
    closedCollarParentIndexValid word fiber71 cert71.parents 0 = true := by
  have cert71_fiber_length : fiber71.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert71, listGetD, cert71_fiber_length]

theorem cert71_row_1 :
    closedCollarParentIndexValid word fiber71 cert71.parents 1 = true := by
  have cert71_fiber_length : fiber71.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert71, listGetD, cert71_fiber_length, cert71_step_1_0, cert71_step_0_1]

theorem cert71_rows :
    closedCollarSpineRowsValid word fiber71 cert71.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert71_fiber_length : fiber71.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert71_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert71_row_1
  · omega

theorem cert71_root :
    closedCollarSpineParentsReachRoot fiber71 cert71 = true := by
  decide

theorem cert71_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert71.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert71 closedStates_eq fiber71_eq cert71_rows cert71_root

def fiber72 : List (List TauState) :=
[
  [stateAt 132, stateAt 164]
, [stateAt 133, stateAt 172]
, [stateAt 180, stateAt 180]
, [stateAt 181, stateAt 188]
, [stateAt 182, stateAt 116]
, [stateAt 183, stateAt 124]
]

theorem fiber72_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.r, LColor.r] = fiber72 := by
  decide

def cert72 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.r, LColor.r],
    root := 0,
    maxDepth := 3,
    parents := [0, 0, 0, 1, 2, 3] }

def cert72_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_1_0 = cert72_layer_0_1_0 := by
  decide

def cert72_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_0_1_1 : List ChainEdge :=
  []

theorem cert72_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_1_1 = cert72_layer_0_1_1 := by
  decide

theorem cert72_component_0_1_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 18 cert72_seen_0_1_0 = cert72_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_1_0 cert72_layer_0_1_0 17 cert72_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 17 cert72_seen_0_1_1 = cert72_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_1_1 cert72_layer_0_1_1_eq 17

theorem cert72_step_0_1 :
    closedCollarIndexStepBool word fiber72 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_1)
    (by decide) (by decide)
    (by simpa [cert72_move_0_1] using cert72_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_0_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_0 = cert72_layer_0_2_0 := by
  decide

def cert72_seen_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_0_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_1 = cert72_layer_0_2_1 := by
  decide

def cert72_seen_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_0_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_2 = cert72_layer_0_2_2 := by
  decide

def cert72_seen_0_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_0_2_3 : List ChainEdge :=
  []

theorem cert72_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_3 = cert72_layer_0_2_3 := by
  decide

theorem cert72_component_0_2_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 18 cert72_seen_0_2_0 = cert72_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_0 cert72_layer_0_2_0 17 cert72_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 17 cert72_seen_0_2_1 = cert72_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_1 cert72_layer_0_2_1 16 cert72_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 16 cert72_seen_0_2_2 = cert72_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_2 cert72_layer_0_2_2 15 cert72_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 15 cert72_seen_0_2_3 = cert72_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_3 cert72_layer_0_2_3_eq 15

theorem cert72_step_0_2 :
    closedCollarIndexStepBool word fiber72 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_2)
    (by decide) (by decide)
    (by simpa [cert72_move_0_2] using cert72_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_0_0 = cert72_layer_1_0_0 := by
  decide

def cert72_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_1_0_1 : List ChainEdge :=
  []

theorem cert72_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_0_1 = cert72_layer_1_0_1 := by
  decide

theorem cert72_component_1_0_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 18 cert72_seen_1_0_0 = cert72_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_0_0 cert72_layer_1_0_0 17 cert72_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 17 cert72_seen_1_0_1 = cert72_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_0_1 cert72_layer_1_0_1_eq 17

theorem cert72_step_1_0 :
    closedCollarIndexStepBool word fiber72 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_0)
    (by decide) (by decide)
    (by simpa [cert72_move_1_0] using cert72_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert72_seen_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_1_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_0 = cert72_layer_1_3_0 := by
  decide

def cert72_seen_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_1_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_1 = cert72_layer_1_3_1 := by
  decide

def cert72_seen_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_1_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert72_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_2 = cert72_layer_1_3_2 := by
  decide

def cert72_seen_1_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert72_layer_1_3_3 : List ChainEdge :=
  []

theorem cert72_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_3 = cert72_layer_1_3_3 := by
  decide

theorem cert72_component_1_3_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 18 cert72_seen_1_3_0 = cert72_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_0 cert72_layer_1_3_0 17 cert72_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 17 cert72_seen_1_3_1 = cert72_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_1 cert72_layer_1_3_1 16 cert72_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 16 cert72_seen_1_3_2 = cert72_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_2 cert72_layer_1_3_2 15 cert72_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 15 cert72_seen_1_3_3 = cert72_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_3 cert72_layer_1_3_3_eq 15

theorem cert72_step_1_3 :
    closedCollarIndexStepBool word fiber72 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_3)
    (by decide) (by decide)
    (by simpa [cert72_move_1_3] using cert72_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_2_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_0 = cert72_layer_2_0_0 := by
  decide

def cert72_seen_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_2_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_1 = cert72_layer_2_0_1 := by
  decide

def cert72_seen_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_2_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_2 = cert72_layer_2_0_2 := by
  decide

def cert72_seen_2_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_2_0_3 : List ChainEdge :=
  []

theorem cert72_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_3 = cert72_layer_2_0_3 := by
  decide

theorem cert72_component_2_0_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 18 cert72_seen_2_0_0 = cert72_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_0 cert72_layer_2_0_0 17 cert72_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 17 cert72_seen_2_0_1 = cert72_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_1 cert72_layer_2_0_1 16 cert72_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 16 cert72_seen_2_0_2 = cert72_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_2 cert72_layer_2_0_2 15 cert72_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 15 cert72_seen_2_0_3 = cert72_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_3 cert72_layer_2_0_3_eq 15

theorem cert72_step_2_0 :
    closedCollarIndexStepBool word fiber72 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_0)
    (by decide) (by decide)
    (by simpa [cert72_move_2_0] using cert72_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_2_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_4_0 = cert72_layer_2_4_0 := by
  decide

def cert72_seen_2_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_4_1 = cert72_layer_2_4_1 := by
  decide

def cert72_seen_2_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_4_2 = cert72_layer_2_4_2 := by
  decide

def cert72_seen_2_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_2_4_3 : List ChainEdge :=
  []

theorem cert72_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_4_3 = cert72_layer_2_4_3 := by
  decide

theorem cert72_component_2_4_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 18 cert72_seen_2_4_0 = cert72_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_4_0 cert72_layer_2_4_0 17 cert72_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 17 cert72_seen_2_4_1 = cert72_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_4_1 cert72_layer_2_4_1 16 cert72_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 16 cert72_seen_2_4_2 = cert72_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_4_2 cert72_layer_2_4_2 15 cert72_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 15 cert72_seen_2_4_3 = cert72_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_4_3 cert72_layer_2_4_3_eq 15

theorem cert72_step_2_4 :
    closedCollarIndexStepBool word fiber72 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_4)
    (by decide) (by decide)
    (by simpa [cert72_move_2_4] using cert72_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert72_seen_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_3_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_0 = cert72_layer_3_1_0 := by
  decide

def cert72_seen_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_3_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_1 = cert72_layer_3_1_1 := by
  decide

def cert72_seen_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_3_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert72_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_2 = cert72_layer_3_1_2 := by
  decide

def cert72_seen_3_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert72_layer_3_1_3 : List ChainEdge :=
  []

theorem cert72_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_3 = cert72_layer_3_1_3 := by
  decide

theorem cert72_component_3_1_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 18 cert72_seen_3_1_0 = cert72_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_0 cert72_layer_3_1_0 17 cert72_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 17 cert72_seen_3_1_1 = cert72_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_1 cert72_layer_3_1_1 16 cert72_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 16 cert72_seen_3_1_2 = cert72_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_2 cert72_layer_3_1_2 15 cert72_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 15 cert72_seen_3_1_3 = cert72_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_3 cert72_layer_3_1_3_eq 15

theorem cert72_step_3_1 :
    closedCollarIndexStepBool word fiber72 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_1)
    (by decide) (by decide)
    (by simpa [cert72_move_3_1] using cert72_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_3_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_5_0 = cert72_layer_3_5_0 := by
  decide

def cert72_seen_3_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_3_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_5_1 = cert72_layer_3_5_1 := by
  decide

def cert72_seen_3_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_3_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_5_2 = cert72_layer_3_5_2 := by
  decide

def cert72_seen_3_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_3_5_3 : List ChainEdge :=
  []

theorem cert72_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_5_3 = cert72_layer_3_5_3 := by
  decide

theorem cert72_component_3_5_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 18 cert72_seen_3_5_0 = cert72_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_5_0 cert72_layer_3_5_0 17 cert72_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 17 cert72_seen_3_5_1 = cert72_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_5_1 cert72_layer_3_5_1 16 cert72_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 16 cert72_seen_3_5_2 = cert72_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_5_2 cert72_layer_3_5_2 15 cert72_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 15 cert72_seen_3_5_3 = cert72_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_5_3 cert72_layer_3_5_3_eq 15

theorem cert72_step_3_5 :
    closedCollarIndexStepBool word fiber72 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_5)
    (by decide) (by decide)
    (by simpa [cert72_move_3_5] using cert72_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert72_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_4_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_2_0 = cert72_layer_4_2_0 := by
  decide

def cert72_seen_4_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_2_1 = cert72_layer_4_2_1 := by
  decide

def cert72_seen_4_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_2_2 = cert72_layer_4_2_2 := by
  decide

def cert72_seen_4_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_4_2_3 : List ChainEdge :=
  []

theorem cert72_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_2_3 = cert72_layer_4_2_3 := by
  decide

theorem cert72_component_4_2_eq :
    closedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 18 cert72_seen_4_2_0 = cert72_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_2_0 cert72_layer_4_2_0 17 cert72_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 17 cert72_seen_4_2_1 = cert72_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_2_1 cert72_layer_4_2_1 16 cert72_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 16 cert72_seen_4_2_2 = cert72_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_2_2 cert72_layer_4_2_2 15 cert72_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 15 cert72_seen_4_2_3 = cert72_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_2_3 cert72_layer_4_2_3_eq 15

theorem cert72_step_4_2 :
    closedCollarIndexStepBool word fiber72 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_4_2)
    (by decide) (by decide)
    (by simpa [cert72_move_4_2] using cert72_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_5_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_3_0 = cert72_layer_5_3_0 := by
  decide

def cert72_seen_5_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_5_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_3_1 = cert72_layer_5_3_1 := by
  decide

def cert72_seen_5_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_5_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_3_2 = cert72_layer_5_3_2 := by
  decide

def cert72_seen_5_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_5_3_3 : List ChainEdge :=
  []

theorem cert72_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_3_3 = cert72_layer_5_3_3 := by
  decide

theorem cert72_component_5_3_eq :
    closedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 18 cert72_seen_5_3_0 = cert72_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_3_0 cert72_layer_5_3_0 17 cert72_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 17 cert72_seen_5_3_1 = cert72_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_3_1 cert72_layer_5_3_1 16 cert72_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 16 cert72_seen_5_3_2 = cert72_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_3_2 cert72_layer_5_3_2 15 cert72_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 15 cert72_seen_5_3_3 = cert72_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_3_3 cert72_layer_5_3_3_eq 15

theorem cert72_step_5_3 :
    closedCollarIndexStepBool word fiber72 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_5_3)
    (by decide) (by decide)
    (by simpa [cert72_move_5_3] using cert72_component_5_3_eq)
    (by decide) (by decide) (by decide)

theorem cert72_row_0 :
    closedCollarParentIndexValid word fiber72 cert72.parents 0 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length]

theorem cert72_row_1 :
    closedCollarParentIndexValid word fiber72 cert72.parents 1 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_1_0, cert72_step_0_1]

theorem cert72_row_2 :
    closedCollarParentIndexValid word fiber72 cert72.parents 2 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_2_0, cert72_step_0_2]

theorem cert72_row_3 :
    closedCollarParentIndexValid word fiber72 cert72.parents 3 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_3_1, cert72_step_1_3]

theorem cert72_row_4 :
    closedCollarParentIndexValid word fiber72 cert72.parents 4 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_4_2, cert72_step_2_4]

theorem cert72_row_5 :
    closedCollarParentIndexValid word fiber72 cert72.parents 5 = true := by
  have cert72_fiber_length : fiber72.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_5_3, cert72_step_3_5]

theorem cert72_rows :
    closedCollarSpineRowsValid word fiber72 cert72.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert72_fiber_length : fiber72.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert72_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert72_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert72_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert72_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert72_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert72_row_5
  · omega

theorem cert72_root :
    closedCollarSpineParentsReachRoot fiber72 cert72 = true := by
  decide

theorem cert72_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.r] := by
  change closedCollarFiberKempeConnected word cert72.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert72 closedStates_eq fiber72_eq cert72_rows cert72_root

theorem cert73_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.r, LColor.b] = [] := by
  decide

theorem cert73_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert73_empty

def fiber74 : List (List TauState) :=
[
  [stateAt 22, stateAt 176]
, [stateAt 23, stateAt 184]
]

theorem fiber74_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.r, LColor.p] = fiber74 := by
  decide

def cert74 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.r, LColor.p],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert74_move_0_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert74_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert74_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert74_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert74_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber74 0 [])
      LColor.r LColor.p cert74_seen_0_1_0 = cert74_layer_0_1_0 := by
  decide

def cert74_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert74_layer_0_1_1 : List ChainEdge :=
  []

theorem cert74_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber74 0 [])
      LColor.r LColor.p cert74_seen_0_1_1 = cert74_layer_0_1_1 := by
  decide

theorem cert74_component_0_1_eq :
    closedCollarComponent word (listGetD fiber74 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert74_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber74 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber74 0 [])
      LColor.r LColor.p 18 cert74_seen_0_1_0 = cert74_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber74 0 []) LColor.r LColor.p
    cert74_seen_0_1_0 cert74_layer_0_1_0 17 cert74_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber74 0 [])
      LColor.r LColor.p 17 cert74_seen_0_1_1 = cert74_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber74 0 []) LColor.r LColor.p
    cert74_seen_0_1_1 cert74_layer_0_1_1_eq 17

theorem cert74_step_0_1 :
    closedCollarIndexStepBool word fiber74 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert74_move_0_1)
    (by decide) (by decide)
    (by simpa [cert74_move_0_1] using cert74_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert74_move_1_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert74_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert74_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert74_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert74_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber74 1 [])
      LColor.r LColor.p cert74_seen_1_0_0 = cert74_layer_1_0_0 := by
  decide

def cert74_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert74_layer_1_0_1 : List ChainEdge :=
  []

theorem cert74_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber74 1 [])
      LColor.r LColor.p cert74_seen_1_0_1 = cert74_layer_1_0_1 := by
  decide

theorem cert74_component_1_0_eq :
    closedCollarComponent word (listGetD fiber74 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = cert74_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber74 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber74 1 [])
      LColor.r LColor.p 18 cert74_seen_1_0_0 = cert74_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber74 1 []) LColor.r LColor.p
    cert74_seen_1_0_0 cert74_layer_1_0_0 17 cert74_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber74 1 [])
      LColor.r LColor.p 17 cert74_seen_1_0_1 = cert74_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber74 1 []) LColor.r LColor.p
    cert74_seen_1_0_1 cert74_layer_1_0_1_eq 17

theorem cert74_step_1_0 :
    closedCollarIndexStepBool word fiber74 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert74_move_1_0)
    (by decide) (by decide)
    (by simpa [cert74_move_1_0] using cert74_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert74_row_0 :
    closedCollarParentIndexValid word fiber74 cert74.parents 0 = true := by
  have cert74_fiber_length : fiber74.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert74, listGetD, cert74_fiber_length]

theorem cert74_row_1 :
    closedCollarParentIndexValid word fiber74 cert74.parents 1 = true := by
  have cert74_fiber_length : fiber74.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert74, listGetD, cert74_fiber_length, cert74_step_1_0, cert74_step_0_1]

theorem cert74_rows :
    closedCollarSpineRowsValid word fiber74 cert74.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert74_fiber_length : fiber74.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert74_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert74_row_1
  · omega

theorem cert74_root :
    closedCollarSpineParentsReachRoot fiber74 cert74 = true := by
  decide

theorem cert74_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.p] := by
  change closedCollarFiberKempeConnected word cert74.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert74 closedStates_eq fiber74_eq cert74_rows cert74_root

theorem cert75_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.b, LColor.r] = [] := by
  decide

theorem cert75_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert75_empty

def fiber76 : List (List TauState) :=
[
  [stateAt 148, stateAt 148]
, [stateAt 149, stateAt 156]
, [stateAt 150, stateAt 48]
, [stateAt 151, stateAt 56]
, [stateAt 164, stateAt 132]
, [stateAt 165, stateAt 140]
]

theorem fiber76_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.b, LColor.b] = fiber76 := by
  decide

def cert76 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.b, LColor.b],
    root := 0,
    maxDepth := 2,
    parents := [0, 0, 1, 0, 0, 1] }

def cert76_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert76_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert76_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_1_0 = cert76_layer_0_1_0 := by
  decide

def cert76_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_0_1_1 : List ChainEdge :=
  []

theorem cert76_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_1_1 = cert76_layer_0_1_1 := by
  decide

theorem cert76_component_0_1_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert76_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 18 cert76_seen_0_1_0 = cert76_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_1_0 cert76_layer_0_1_0 17 cert76_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 17 cert76_seen_0_1_1 = cert76_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_1_1 cert76_layer_0_1_1_eq 17

theorem cert76_step_0_1 :
    closedCollarIndexStepBool word fiber76 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_1)
    (by decide) (by decide)
    (by simpa [cert76_move_0_1] using cert76_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_0_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_0_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_0_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_3_0 = cert76_layer_0_3_0 := by
  decide

def cert76_seen_0_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_0_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_0_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_3_1 = cert76_layer_0_3_1 := by
  decide

def cert76_seen_0_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_0_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_0_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_3_2 = cert76_layer_0_3_2 := by
  decide

def cert76_seen_0_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_0_3_3 : List ChainEdge :=
  []

theorem cert76_layer_0_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_3_3 = cert76_layer_0_3_3 := by
  decide

theorem cert76_component_0_3_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_0_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 18 cert76_seen_0_3_0 = cert76_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_3_0 cert76_layer_0_3_0 17 cert76_layer_0_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 17 cert76_seen_0_3_1 = cert76_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_3_1 cert76_layer_0_3_1 16 cert76_layer_0_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 16 cert76_seen_0_3_2 = cert76_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_3_2 cert76_layer_0_3_2 15 cert76_layer_0_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 15 cert76_seen_0_3_3 = cert76_component_0_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_3_3 cert76_layer_0_3_3_eq 15

theorem cert76_step_0_3 :
    closedCollarIndexStepBool word fiber76 0 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_3)
    (by decide) (by decide)
    (by simpa [cert76_move_0_3] using cert76_component_0_3_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_4_0 = cert76_layer_0_4_0 := by
  decide

def cert76_seen_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_4_1 = cert76_layer_0_4_1 := by
  decide

def cert76_seen_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_0_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_4_2 = cert76_layer_0_4_2 := by
  decide

def cert76_seen_0_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_0_4_3 : List ChainEdge :=
  []

theorem cert76_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_4_3 = cert76_layer_0_4_3 := by
  decide

theorem cert76_component_0_4_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert76_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 18 cert76_seen_0_4_0 = cert76_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_4_0 cert76_layer_0_4_0 17 cert76_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 17 cert76_seen_0_4_1 = cert76_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_4_1 cert76_layer_0_4_1 16 cert76_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 16 cert76_seen_0_4_2 = cert76_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_4_2 cert76_layer_0_4_2 15 cert76_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 15 cert76_seen_0_4_3 = cert76_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_4_3 cert76_layer_0_4_3_eq 15

theorem cert76_step_0_4 :
    closedCollarIndexStepBool word fiber76 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_4)
    (by decide) (by decide)
    (by simpa [cert76_move_0_4] using cert76_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert76_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert76_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_0_0 = cert76_layer_1_0_0 := by
  decide

def cert76_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_1_0_1 : List ChainEdge :=
  []

theorem cert76_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_0_1 = cert76_layer_1_0_1 := by
  decide

theorem cert76_component_1_0_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert76_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 18 cert76_seen_1_0_0 = cert76_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_0_0 cert76_layer_1_0_0 17 cert76_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 17 cert76_seen_1_0_1 = cert76_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_0_1 cert76_layer_1_0_1_eq 17

theorem cert76_step_1_0 :
    closedCollarIndexStepBool word fiber76 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_0)
    (by decide) (by decide)
    (by simpa [cert76_move_1_0] using cert76_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_1_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_1_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_1_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_2_0 = cert76_layer_1_2_0 := by
  decide

def cert76_seen_1_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_1_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_1_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_2_1 = cert76_layer_1_2_1 := by
  decide

def cert76_seen_1_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_1_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_1_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_2_2 = cert76_layer_1_2_2 := by
  decide

def cert76_seen_1_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_1_2_3 : List ChainEdge :=
  []

theorem cert76_layer_1_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_2_3 = cert76_layer_1_2_3 := by
  decide

theorem cert76_component_1_2_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_1_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 18 cert76_seen_1_2_0 = cert76_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_2_0 cert76_layer_1_2_0 17 cert76_layer_1_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 17 cert76_seen_1_2_1 = cert76_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_2_1 cert76_layer_1_2_1 16 cert76_layer_1_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 16 cert76_seen_1_2_2 = cert76_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_2_2 cert76_layer_1_2_2 15 cert76_layer_1_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 15 cert76_seen_1_2_3 = cert76_component_1_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_2_3 cert76_layer_1_2_3_eq 15

theorem cert76_step_1_2 :
    closedCollarIndexStepBool word fiber76 1 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_2)
    (by decide) (by decide)
    (by simpa [cert76_move_1_2] using cert76_component_1_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_5_0 = cert76_layer_1_5_0 := by
  decide

def cert76_seen_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_5_1 = cert76_layer_1_5_1 := by
  decide

def cert76_seen_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_1_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_5_2 = cert76_layer_1_5_2 := by
  decide

def cert76_seen_1_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_1_5_3 : List ChainEdge :=
  []

theorem cert76_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_5_3 = cert76_layer_1_5_3 := by
  decide

theorem cert76_component_1_5_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert76_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 18 cert76_seen_1_5_0 = cert76_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_5_0 cert76_layer_1_5_0 17 cert76_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 17 cert76_seen_1_5_1 = cert76_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_5_1 cert76_layer_1_5_1 16 cert76_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 16 cert76_seen_1_5_2 = cert76_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_5_2 cert76_layer_1_5_2 15 cert76_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 15 cert76_seen_1_5_3 = cert76_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_5_3 cert76_layer_1_5_3_eq 15

theorem cert76_step_1_5 :
    closedCollarIndexStepBool word fiber76 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_5)
    (by decide) (by decide)
    (by simpa [cert76_move_1_5] using cert76_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_2_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_2_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_2_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_1_0 = cert76_layer_2_1_0 := by
  decide

def cert76_seen_2_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_2_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_2_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_1_1 = cert76_layer_2_1_1 := by
  decide

def cert76_seen_2_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_2_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_2_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_1_2 = cert76_layer_2_1_2 := by
  decide

def cert76_seen_2_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_2_1_3 : List ChainEdge :=
  []

theorem cert76_layer_2_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_1_3 = cert76_layer_2_1_3 := by
  decide

theorem cert76_component_2_1_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_2_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 18 cert76_seen_2_1_0 = cert76_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_1_0 cert76_layer_2_1_0 17 cert76_layer_2_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 17 cert76_seen_2_1_1 = cert76_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_1_1 cert76_layer_2_1_1 16 cert76_layer_2_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 16 cert76_seen_2_1_2 = cert76_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_1_2 cert76_layer_2_1_2 15 cert76_layer_2_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 15 cert76_seen_2_1_3 = cert76_component_2_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_1_3 cert76_layer_2_1_3_eq 15

theorem cert76_step_2_1 :
    closedCollarIndexStepBool word fiber76 2 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_1)
    (by decide) (by decide)
    (by simpa [cert76_move_2_1] using cert76_component_2_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_3_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_3_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_3_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_3_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_0_0 = cert76_layer_3_0_0 := by
  decide

def cert76_seen_3_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_3_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_3_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_0_1 = cert76_layer_3_0_1 := by
  decide

def cert76_seen_3_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_3_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_3_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_0_2 = cert76_layer_3_0_2 := by
  decide

def cert76_seen_3_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_3_0_3 : List ChainEdge :=
  []

theorem cert76_layer_3_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_0_3 = cert76_layer_3_0_3 := by
  decide

theorem cert76_component_3_0_eq :
    closedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_3_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 18 cert76_seen_3_0_0 = cert76_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_0_0 cert76_layer_3_0_0 17 cert76_layer_3_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 17 cert76_seen_3_0_1 = cert76_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_0_1 cert76_layer_3_0_1 16 cert76_layer_3_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 16 cert76_seen_3_0_2 = cert76_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_0_2 cert76_layer_3_0_2 15 cert76_layer_3_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 15 cert76_seen_3_0_3 = cert76_component_3_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_0_3 cert76_layer_3_0_3_eq 15

theorem cert76_step_3_0 :
    closedCollarIndexStepBool word fiber76 3 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_3_0)
    (by decide) (by decide)
    (by simpa [cert76_move_3_0] using cert76_component_3_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_4_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.b cert76_seen_4_0_0 = cert76_layer_4_0_0 := by
  decide

def cert76_seen_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.b cert76_seen_4_0_1 = cert76_layer_4_0_1 := by
  decide

def cert76_seen_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_4_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.b cert76_seen_4_0_2 = cert76_layer_4_0_2 := by
  decide

def cert76_seen_4_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_4_0_3 : List ChainEdge :=
  []

theorem cert76_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.b cert76_seen_4_0_3 = cert76_layer_4_0_3 := by
  decide

theorem cert76_component_4_0_eq :
    closedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert76_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.b 18 cert76_seen_4_0_0 = cert76_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.b
    cert76_seen_4_0_0 cert76_layer_4_0_0 17 cert76_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.b 17 cert76_seen_4_0_1 = cert76_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.b
    cert76_seen_4_0_1 cert76_layer_4_0_1 16 cert76_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.b 16 cert76_seen_4_0_2 = cert76_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.b
    cert76_seen_4_0_2 cert76_layer_4_0_2 15 cert76_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.b 15 cert76_seen_4_0_3 = cert76_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 4 []) LColor.r LColor.b
    cert76_seen_4_0_3 cert76_layer_4_0_3_eq 15

theorem cert76_step_4_0 :
    closedCollarIndexStepBool word fiber76 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_4_0)
    (by decide) (by decide)
    (by simpa [cert76_move_4_0] using cert76_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_5_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.b cert76_seen_5_1_0 = cert76_layer_5_1_0 := by
  decide

def cert76_seen_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.b cert76_seen_5_1_1 = cert76_layer_5_1_1 := by
  decide

def cert76_seen_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_5_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.b cert76_seen_5_1_2 = cert76_layer_5_1_2 := by
  decide

def cert76_seen_5_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_5_1_3 : List ChainEdge :=
  []

theorem cert76_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.b cert76_seen_5_1_3 = cert76_layer_5_1_3 := by
  decide

theorem cert76_component_5_1_eq :
    closedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert76_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.b 18 cert76_seen_5_1_0 = cert76_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.b
    cert76_seen_5_1_0 cert76_layer_5_1_0 17 cert76_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.b 17 cert76_seen_5_1_1 = cert76_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.b
    cert76_seen_5_1_1 cert76_layer_5_1_1 16 cert76_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.b 16 cert76_seen_5_1_2 = cert76_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.b
    cert76_seen_5_1_2 cert76_layer_5_1_2 15 cert76_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.b 15 cert76_seen_5_1_3 = cert76_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 5 []) LColor.r LColor.b
    cert76_seen_5_1_3 cert76_layer_5_1_3_eq 15

theorem cert76_step_5_1 :
    closedCollarIndexStepBool word fiber76 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_5_1)
    (by decide) (by decide)
    (by simpa [cert76_move_5_1] using cert76_component_5_1_eq)
    (by decide) (by decide) (by decide)

theorem cert76_row_0 :
    closedCollarParentIndexValid word fiber76 cert76.parents 0 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length]

theorem cert76_row_1 :
    closedCollarParentIndexValid word fiber76 cert76.parents 1 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_1_0, cert76_step_0_1]

theorem cert76_row_2 :
    closedCollarParentIndexValid word fiber76 cert76.parents 2 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_2_1, cert76_step_1_2]

theorem cert76_row_3 :
    closedCollarParentIndexValid word fiber76 cert76.parents 3 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_3_0, cert76_step_0_3]

theorem cert76_row_4 :
    closedCollarParentIndexValid word fiber76 cert76.parents 4 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_4_0, cert76_step_0_4]

theorem cert76_row_5 :
    closedCollarParentIndexValid word fiber76 cert76.parents 5 = true := by
  have cert76_fiber_length : fiber76.length = 6 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_5_1, cert76_step_1_5]

theorem cert76_rows :
    closedCollarSpineRowsValid word fiber76 cert76.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert76_fiber_length : fiber76.length = 6 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert76_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert76_row_1
  by_cases h2 : idx = 2
  · subst idx
    exact cert76_row_2
  by_cases h3 : idx = 3
  · subst idx
    exact cert76_row_3
  by_cases h4 : idx = 4
  · subst idx
    exact cert76_row_4
  by_cases h5 : idx = 5
  · subst idx
    exact cert76_row_5
  · omega

theorem cert76_root :
    closedCollarSpineParentsReachRoot fiber76 cert76 = true := by
  decide

theorem cert76_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.b] := by
  change closedCollarFiberKempeConnected word cert76.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert76 closedStates_eq fiber76_eq cert76_rows cert76_root

def fiber77 : List (List TauState) :=
[
  [stateAt 84, stateAt 144]
, [stateAt 85, stateAt 152]
]

theorem fiber77_eq :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.b, LColor.p] = fiber77 := by
  decide

def cert77 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.b, LColor.p],
    root := 0,
    maxDepth := 1,
    parents := [0, 0] }

def cert77_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert77_component_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert77_seen_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert77_layer_0_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert77_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber77 0 [])
      LColor.b LColor.p cert77_seen_0_1_0 = cert77_layer_0_1_0 := by
  decide

def cert77_seen_0_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert77_layer_0_1_1 : List ChainEdge :=
  []

theorem cert77_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber77 0 [])
      LColor.b LColor.p cert77_seen_0_1_1 = cert77_layer_0_1_1 := by
  decide

theorem cert77_component_0_1_eq :
    closedCollarComponent word (listGetD fiber77 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert77_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber77 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber77 0 [])
      LColor.b LColor.p 18 cert77_seen_0_1_0 = cert77_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber77 0 []) LColor.b LColor.p
    cert77_seen_0_1_0 cert77_layer_0_1_0 17 cert77_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber77 0 [])
      LColor.b LColor.p 17 cert77_seen_0_1_1 = cert77_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber77 0 []) LColor.b LColor.p
    cert77_seen_0_1_1 cert77_layer_0_1_1_eq 17

theorem cert77_step_0_1 :
    closedCollarIndexStepBool word fiber77 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert77_move_0_1)
    (by decide) (by decide)
    (by simpa [cert77_move_0_1] using cert77_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert77_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert77_component_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert77_seen_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert77_layer_1_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert77_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber77 1 [])
      LColor.b LColor.p cert77_seen_1_0_0 = cert77_layer_1_0_0 := by
  decide

def cert77_seen_1_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert77_layer_1_0_1 : List ChainEdge :=
  []

theorem cert77_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber77 1 [])
      LColor.b LColor.p cert77_seen_1_0_1 = cert77_layer_1_0_1 := by
  decide

theorem cert77_component_1_0_eq :
    closedCollarComponent word (listGetD fiber77 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert77_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber77 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber77 1 [])
      LColor.b LColor.p 18 cert77_seen_1_0_0 = cert77_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber77 1 []) LColor.b LColor.p
    cert77_seen_1_0_0 cert77_layer_1_0_0 17 cert77_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber77 1 [])
      LColor.b LColor.p 17 cert77_seen_1_0_1 = cert77_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber77 1 []) LColor.b LColor.p
    cert77_seen_1_0_1 cert77_layer_1_0_1_eq 17

theorem cert77_step_1_0 :
    closedCollarIndexStepBool word fiber77 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert77_move_1_0)
    (by decide) (by decide)
    (by simpa [cert77_move_1_0] using cert77_component_1_0_eq)
    (by decide) (by decide) (by decide)

theorem cert77_row_0 :
    closedCollarParentIndexValid word fiber77 cert77.parents 0 = true := by
  have cert77_fiber_length : fiber77.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert77, listGetD, cert77_fiber_length]

theorem cert77_row_1 :
    closedCollarParentIndexValid word fiber77 cert77.parents 1 = true := by
  have cert77_fiber_length : fiber77.length = 2 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert77, listGetD, cert77_fiber_length, cert77_step_1_0, cert77_step_0_1]

theorem cert77_rows :
    closedCollarSpineRowsValid word fiber77 cert77.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert77_fiber_length : fiber77.length = 2 := by decide

  by_cases h0 : idx = 0
  · subst idx
    exact cert77_row_0
  by_cases h1 : idx = 1
  · subst idx
    exact cert77_row_1
  · omega

theorem cert77_root :
    closedCollarSpineParentsReachRoot fiber77 cert77 = true := by
  decide

theorem cert77_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.p] := by
  change closedCollarFiberKempeConnected word cert77.key
  exact closedCollarFiberKempeConnected_of_spineRowsForFiber cert77 closedStates_eq fiber77_eq cert77_rows cert77_root

theorem cert78_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.p, LColor.r] = [] := by
  decide

theorem cert78_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert78_empty

theorem cert79_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.p, LColor.b] = [] := by
  decide

theorem cert79_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert79_empty

theorem cert80_empty :
    closedCollarFiberFrom word closedStates [LColor.p, LColor.p, LColor.p, LColor.p] = [] := by
  decide

theorem cert80_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil closedStates_eq cert80_empty

theorem targetForWord : closedCollarS2BridgeTargetForWord word := by
  intro key hkey
  have hcases :
      key = [LColor.r, LColor.r, LColor.r, LColor.r] ∨
        key = [LColor.r, LColor.r, LColor.r, LColor.b] ∨
          key = [LColor.r, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.p] := by
    simpa [colorAssignments4, bindList, colors] using hkey
  rcases hcases with h0 | hcases
  · simpa [h0] using cert0_connected
  rcases hcases with h1 | hcases
  · simpa [h1] using cert1_connected
  rcases hcases with h2 | hcases
  · simpa [h2] using cert2_connected
  rcases hcases with h3 | hcases
  · simpa [h3] using cert3_connected
  rcases hcases with h4 | hcases
  · simpa [h4] using cert4_connected
  rcases hcases with h5 | hcases
  · simpa [h5] using cert5_connected
  rcases hcases with h6 | hcases
  · simpa [h6] using cert6_connected
  rcases hcases with h7 | hcases
  · simpa [h7] using cert7_connected
  rcases hcases with h8 | hcases
  · simpa [h8] using cert8_connected
  rcases hcases with h9 | hcases
  · simpa [h9] using cert9_connected
  rcases hcases with h10 | hcases
  · simpa [h10] using cert10_connected
  rcases hcases with h11 | hcases
  · simpa [h11] using cert11_connected
  rcases hcases with h12 | hcases
  · simpa [h12] using cert12_connected
  rcases hcases with h13 | hcases
  · simpa [h13] using cert13_connected
  rcases hcases with h14 | hcases
  · simpa [h14] using cert14_connected
  rcases hcases with h15 | hcases
  · simpa [h15] using cert15_connected
  rcases hcases with h16 | hcases
  · simpa [h16] using cert16_connected
  rcases hcases with h17 | hcases
  · simpa [h17] using cert17_connected
  rcases hcases with h18 | hcases
  · simpa [h18] using cert18_connected
  rcases hcases with h19 | hcases
  · simpa [h19] using cert19_connected
  rcases hcases with h20 | hcases
  · simpa [h20] using cert20_connected
  rcases hcases with h21 | hcases
  · simpa [h21] using cert21_connected
  rcases hcases with h22 | hcases
  · simpa [h22] using cert22_connected
  rcases hcases with h23 | hcases
  · simpa [h23] using cert23_connected
  rcases hcases with h24 | hcases
  · simpa [h24] using cert24_connected
  rcases hcases with h25 | hcases
  · simpa [h25] using cert25_connected
  rcases hcases with h26 | hcases
  · simpa [h26] using cert26_connected
  rcases hcases with h27 | hcases
  · simpa [h27] using cert27_connected
  rcases hcases with h28 | hcases
  · simpa [h28] using cert28_connected
  rcases hcases with h29 | hcases
  · simpa [h29] using cert29_connected
  rcases hcases with h30 | hcases
  · simpa [h30] using cert30_connected
  rcases hcases with h31 | hcases
  · simpa [h31] using cert31_connected
  rcases hcases with h32 | hcases
  · simpa [h32] using cert32_connected
  rcases hcases with h33 | hcases
  · simpa [h33] using cert33_connected
  rcases hcases with h34 | hcases
  · simpa [h34] using cert34_connected
  rcases hcases with h35 | hcases
  · simpa [h35] using cert35_connected
  rcases hcases with h36 | hcases
  · simpa [h36] using cert36_connected
  rcases hcases with h37 | hcases
  · simpa [h37] using cert37_connected
  rcases hcases with h38 | hcases
  · simpa [h38] using cert38_connected
  rcases hcases with h39 | hcases
  · simpa [h39] using cert39_connected
  rcases hcases with h40 | hcases
  · simpa [h40] using cert40_connected
  rcases hcases with h41 | hcases
  · simpa [h41] using cert41_connected
  rcases hcases with h42 | hcases
  · simpa [h42] using cert42_connected
  rcases hcases with h43 | hcases
  · simpa [h43] using cert43_connected
  rcases hcases with h44 | hcases
  · simpa [h44] using cert44_connected
  rcases hcases with h45 | hcases
  · simpa [h45] using cert45_connected
  rcases hcases with h46 | hcases
  · simpa [h46] using cert46_connected
  rcases hcases with h47 | hcases
  · simpa [h47] using cert47_connected
  rcases hcases with h48 | hcases
  · simpa [h48] using cert48_connected
  rcases hcases with h49 | hcases
  · simpa [h49] using cert49_connected
  rcases hcases with h50 | hcases
  · simpa [h50] using cert50_connected
  rcases hcases with h51 | hcases
  · simpa [h51] using cert51_connected
  rcases hcases with h52 | hcases
  · simpa [h52] using cert52_connected
  rcases hcases with h53 | hcases
  · simpa [h53] using cert53_connected
  rcases hcases with h54 | hcases
  · simpa [h54] using cert54_connected
  rcases hcases with h55 | hcases
  · simpa [h55] using cert55_connected
  rcases hcases with h56 | hcases
  · simpa [h56] using cert56_connected
  rcases hcases with h57 | hcases
  · simpa [h57] using cert57_connected
  rcases hcases with h58 | hcases
  · simpa [h58] using cert58_connected
  rcases hcases with h59 | hcases
  · simpa [h59] using cert59_connected
  rcases hcases with h60 | hcases
  · simpa [h60] using cert60_connected
  rcases hcases with h61 | hcases
  · simpa [h61] using cert61_connected
  rcases hcases with h62 | hcases
  · simpa [h62] using cert62_connected
  rcases hcases with h63 | hcases
  · simpa [h63] using cert63_connected
  rcases hcases with h64 | hcases
  · simpa [h64] using cert64_connected
  rcases hcases with h65 | hcases
  · simpa [h65] using cert65_connected
  rcases hcases with h66 | hcases
  · simpa [h66] using cert66_connected
  rcases hcases with h67 | hcases
  · simpa [h67] using cert67_connected
  rcases hcases with h68 | hcases
  · simpa [h68] using cert68_connected
  rcases hcases with h69 | hcases
  · simpa [h69] using cert69_connected
  rcases hcases with h70 | hcases
  · simpa [h70] using cert70_connected
  rcases hcases with h71 | hcases
  · simpa [h71] using cert71_connected
  rcases hcases with h72 | hcases
  · simpa [h72] using cert72_connected
  rcases hcases with h73 | hcases
  · simpa [h73] using cert73_connected
  rcases hcases with h74 | hcases
  · simpa [h74] using cert74_connected
  rcases hcases with h75 | hcases
  · simpa [h75] using cert75_connected
  rcases hcases with h76 | hcases
  · simpa [h76] using cert76_connected
  rcases hcases with h77 | hcases
  · simpa [h77] using cert77_connected
  rcases hcases with h78 | hcases
  · simpa [h78] using cert78_connected
  rcases hcases with h79 | hcases
  · simpa [h79] using cert79_connected
  simpa [hcases] using cert80_connected

end GoertzelLemma818ClosedCollarS2Word3
end Mettapedia.GraphTheory.FourColor
