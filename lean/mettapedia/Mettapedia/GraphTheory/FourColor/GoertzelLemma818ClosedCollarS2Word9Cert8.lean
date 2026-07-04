import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast8 : List TauState :=
  [stateAt 3, stateAt 11, stateAt 19, stateAt 27, stateAt 67, stateAt 75, stateAt 83, stateAt 91]

theorem keyedLast8_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.p, LColor.p]) =
      keyedLast8 := by
  decide

def fiber8OuterChunks : List (List (List TauState)) :=
[
  []
, [
  [stateAt 24, stateAt 156, stateAt 91]
, [stateAt 24, stateAt 157, stateAt 83]
, [stateAt 24, stateAt 158, stateAt 75]
, [stateAt 24, stateAt 159, stateAt 67]
, [stateAt 24, stateAt 172, stateAt 27]
, [stateAt 24, stateAt 173, stateAt 19]
, [stateAt 24, stateAt 174, stateAt 11]
, [stateAt 24, stateAt 175, stateAt 3]
, [stateAt 25, stateAt 148, stateAt 91]
, [stateAt 25, stateAt 149, stateAt 83]
, [stateAt 25, stateAt 150, stateAt 75]
, [stateAt 25, stateAt 151, stateAt 67]
, [stateAt 25, stateAt 164, stateAt 27]
, [stateAt 25, stateAt 165, stateAt 19]
, [stateAt 25, stateAt 166, stateAt 11]
, [stateAt 25, stateAt 167, stateAt 3]
, [stateAt 26, stateAt 140, stateAt 91]
, [stateAt 26, stateAt 141, stateAt 83]
, [stateAt 26, stateAt 142, stateAt 75]
, [stateAt 26, stateAt 143, stateAt 67]
, [stateAt 26, stateAt 188, stateAt 27]
, [stateAt 26, stateAt 189, stateAt 19]
, [stateAt 26, stateAt 190, stateAt 11]
, [stateAt 26, stateAt 191, stateAt 3]
, [stateAt 27, stateAt 132, stateAt 91]
, [stateAt 27, stateAt 133, stateAt 83]
, [stateAt 27, stateAt 134, stateAt 75]
, [stateAt 27, stateAt 135, stateAt 67]
, [stateAt 27, stateAt 180, stateAt 27]
, [stateAt 27, stateAt 181, stateAt 19]
, [stateAt 27, stateAt 182, stateAt 11]
, [stateAt 27, stateAt 183, stateAt 3]
]
, [
  [stateAt 40, stateAt 108, stateAt 27]
, [stateAt 40, stateAt 109, stateAt 19]
, [stateAt 40, stateAt 110, stateAt 11]
, [stateAt 40, stateAt 111, stateAt 3]
, [stateAt 41, stateAt 100, stateAt 27]
, [stateAt 41, stateAt 101, stateAt 19]
, [stateAt 41, stateAt 102, stateAt 11]
, [stateAt 41, stateAt 103, stateAt 3]
, [stateAt 42, stateAt 124, stateAt 27]
, [stateAt 42, stateAt 125, stateAt 19]
, [stateAt 42, stateAt 126, stateAt 11]
, [stateAt 42, stateAt 127, stateAt 3]
, [stateAt 43, stateAt 116, stateAt 27]
, [stateAt 43, stateAt 117, stateAt 19]
, [stateAt 43, stateAt 118, stateAt 11]
, [stateAt 43, stateAt 119, stateAt 3]
]
, []
, []
, []
, []
, []
, []
, []
, []
, []
]

def fiber8 : List (List TauState) :=
  fiber8OuterChunks.flatten

theorem fiber8_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 0 []) =
      listGetD fiber8OuterChunks 0 [] := by
  decide

theorem fiber8_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 1 []) =
      listGetD fiber8OuterChunks 1 [] := by
  decide

theorem fiber8_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 2 []) =
      listGetD fiber8OuterChunks 2 [] := by
  decide

theorem fiber8_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 3 []) =
      listGetD fiber8OuterChunks 3 [] := by
  decide

theorem fiber8_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 4 []) =
      listGetD fiber8OuterChunks 4 [] := by
  decide

theorem fiber8_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 5 []) =
      listGetD fiber8OuterChunks 5 [] := by
  decide

theorem fiber8_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 6 []) =
      listGetD fiber8OuterChunks 6 [] := by
  decide

theorem fiber8_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 7 []) =
      listGetD fiber8OuterChunks 7 [] := by
  decide

theorem fiber8_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 8 []) =
      listGetD fiber8OuterChunks 8 [] := by
  decide

theorem fiber8_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 9 []) =
      listGetD fiber8OuterChunks 9 [] := by
  decide

theorem fiber8_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 10 []) =
      listGetD fiber8OuterChunks 10 [] := by
  decide

theorem fiber8_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks 11 []) =
      listGetD fiber8OuterChunks 11 [] := by
  decide

theorem fiber8_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast8
        (listGetD tauStateChunks idx []) =
      listGetD fiber8OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber8_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber8_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber8_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber8_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber8_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber8_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber8_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber8_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber8_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber8_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber8_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber8_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber8_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast8 =
      fiber8 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast8 tauStateChunks fiber8OuterChunks
    tauStateChunks_eq (by rfl) fiber8_outer_get
  simpa [fiber8] using h

theorem fiber8_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.p, LColor.p] = fiber8 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.p, LColor.p] keyedLast8_eq
  exact hfrom.trans fiber8_keyedFrom_eq

theorem fiber8_eq :
    closedCollarFiber word [LColor.r, LColor.r, LColor.p, LColor.p] = fiber8 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.p, LColor.p]
  exact hfast.trans fiber8_keyed_eq

def cert8 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.p, LColor.p],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 1, 0, 0, 1, 4, 3, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 32, 33, 34, 35] }

def cert8_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert8_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert8_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert8_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_0 = cert8_layer_0_1_0 := by
  decide

def cert8_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_layer_0_1_1 : List ChainEdge :=
  []

theorem cert8_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_1 = cert8_layer_0_1_1 := by
  decide

theorem cert8_component_0_1_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert8_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 27 cert8_seen_0_1_0 = cert8_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_1_0 cert8_layer_0_1_0 26 cert8_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 26 cert8_seen_0_1_1 = cert8_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_1_1 cert8_layer_0_1_1_eq 26

theorem cert8_step_0_1 :
    closedCollarIndexStepBool word fiber8 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_1)
    (by decide) (by decide)
    (by simpa [cert8_move_0_1] using cert8_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_0_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_0_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_0_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_3_0 = cert8_layer_0_3_0 := by
  decide

def cert8_seen_0_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_0_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_3_1 = cert8_layer_0_3_1 := by
  decide

def cert8_seen_0_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_0_3_2 : List ChainEdge :=
  []

theorem cert8_layer_0_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_3_2 = cert8_layer_0_3_2 := by
  decide

theorem cert8_component_0_3_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_0_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 27 cert8_seen_0_3_0 = cert8_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_3_0 cert8_layer_0_3_0 26 cert8_layer_0_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 26 cert8_seen_0_3_1 = cert8_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_3_1 cert8_layer_0_3_1 25 cert8_layer_0_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 25 cert8_seen_0_3_2 = cert8_component_0_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_3_2 cert8_layer_0_3_2_eq 25

theorem cert8_step_0_3 :
    closedCollarIndexStepBool word fiber8 0 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_3)
    (by decide) (by decide)
    (by simpa [cert8_move_0_3] using cert8_component_0_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_0_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_0_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_0_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_4_0 = cert8_layer_0_4_0 := by
  decide

def cert8_seen_0_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_0_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_4_1 = cert8_layer_0_4_1 := by
  decide

def cert8_seen_0_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_0_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_4_2 = cert8_layer_0_4_2 := by
  decide

def cert8_seen_0_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_0_4_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_4_3 = cert8_layer_0_4_3 := by
  decide

def cert8_seen_0_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_0_4_4 : List ChainEdge :=
  []

theorem cert8_layer_0_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_4_4 = cert8_layer_0_4_4 := by
  decide

theorem cert8_component_0_4_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 27 cert8_seen_0_4_0 = cert8_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_4_0 cert8_layer_0_4_0 26 cert8_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 26 cert8_seen_0_4_1 = cert8_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_4_1 cert8_layer_0_4_1 25 cert8_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 25 cert8_seen_0_4_2 = cert8_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_4_2 cert8_layer_0_4_2 24 cert8_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 24 cert8_seen_0_4_3 = cert8_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_4_3 cert8_layer_0_4_3 23 cert8_layer_0_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 23 cert8_seen_0_4_4 = cert8_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_4_4 cert8_layer_0_4_4_eq 23

theorem cert8_step_0_4 :
    closedCollarIndexStepBool word fiber8 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_4)
    (by decide) (by decide)
    (by simpa [cert8_move_0_4] using cert8_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_0_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_0_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_0_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_0_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_8_0 = cert8_layer_0_8_0 := by
  decide

def cert8_seen_0_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_0_8_1 : List ChainEdge :=
  []

theorem cert8_layer_0_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_8_1 = cert8_layer_0_8_1 := by
  decide

theorem cert8_component_0_8_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_0_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 27 cert8_seen_0_8_0 = cert8_component_0_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_8_0 cert8_layer_0_8_0 26 cert8_layer_0_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 26 cert8_seen_0_8_1 = cert8_component_0_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_8_1 cert8_layer_0_8_1_eq 26

theorem cert8_step_0_8 :
    closedCollarIndexStepBool word fiber8 0 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_8)
    (by decide) (by decide)
    (by simpa [cert8_move_0_8] using cert8_component_0_8_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_0_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_0_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_16_0 = cert8_layer_0_16_0 := by
  decide

def cert8_seen_0_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_0_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_16_1 = cert8_layer_0_16_1 := by
  decide

def cert8_seen_0_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_0_16_2 : List ChainEdge :=
  []

theorem cert8_layer_0_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_16_2 = cert8_layer_0_16_2 := by
  decide

theorem cert8_component_0_16_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_0_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 27 cert8_seen_0_16_0 = cert8_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_16_0 cert8_layer_0_16_0 26 cert8_layer_0_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 26 cert8_seen_0_16_1 = cert8_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_16_1 cert8_layer_0_16_1 25 cert8_layer_0_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 25 cert8_seen_0_16_2 = cert8_component_0_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_16_2 cert8_layer_0_16_2_eq 25

theorem cert8_step_0_16 :
    closedCollarIndexStepBool word fiber8 0 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_16)
    (by decide) (by decide)
    (by simpa [cert8_move_0_16] using cert8_component_0_16_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert8_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert8_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert8_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_0 = cert8_layer_1_0_0 := by
  decide

def cert8_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_layer_1_0_1 : List ChainEdge :=
  []

theorem cert8_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_1 = cert8_layer_1_0_1 := by
  decide

theorem cert8_component_1_0_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert8_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 27 cert8_seen_1_0_0 = cert8_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_0_0 cert8_layer_1_0_0 26 cert8_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 26 cert8_seen_1_0_1 = cert8_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_0_1 cert8_layer_1_0_1_eq 26

theorem cert8_step_1_0 :
    closedCollarIndexStepBool word fiber8 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_0)
    (by decide) (by decide)
    (by simpa [cert8_move_1_0] using cert8_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_1_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_1_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_1_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_2_0 = cert8_layer_1_2_0 := by
  decide

def cert8_seen_1_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_1_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_2_1 = cert8_layer_1_2_1 := by
  decide

def cert8_seen_1_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_1_2_2 : List ChainEdge :=
  []

theorem cert8_layer_1_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_2_2 = cert8_layer_1_2_2 := by
  decide

theorem cert8_component_1_2_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_1_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 27 cert8_seen_1_2_0 = cert8_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_2_0 cert8_layer_1_2_0 26 cert8_layer_1_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 26 cert8_seen_1_2_1 = cert8_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_2_1 cert8_layer_1_2_1 25 cert8_layer_1_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 25 cert8_seen_1_2_2 = cert8_component_1_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_2_2 cert8_layer_1_2_2_eq 25

theorem cert8_step_1_2 :
    closedCollarIndexStepBool word fiber8 1 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_2)
    (by decide) (by decide)
    (by simpa [cert8_move_1_2] using cert8_component_1_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_1_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_1_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_1_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_5_0 = cert8_layer_1_5_0 := by
  decide

def cert8_seen_1_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_1_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_5_1 = cert8_layer_1_5_1 := by
  decide

def cert8_seen_1_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_1_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_5_2 = cert8_layer_1_5_2 := by
  decide

def cert8_seen_1_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_1_5_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_5_3 = cert8_layer_1_5_3 := by
  decide

def cert8_seen_1_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_1_5_4 : List ChainEdge :=
  []

theorem cert8_layer_1_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_5_4 = cert8_layer_1_5_4 := by
  decide

theorem cert8_component_1_5_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 27 cert8_seen_1_5_0 = cert8_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_5_0 cert8_layer_1_5_0 26 cert8_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 26 cert8_seen_1_5_1 = cert8_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_5_1 cert8_layer_1_5_1 25 cert8_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 25 cert8_seen_1_5_2 = cert8_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_5_2 cert8_layer_1_5_2 24 cert8_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 24 cert8_seen_1_5_3 = cert8_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_5_3 cert8_layer_1_5_3 23 cert8_layer_1_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 23 cert8_seen_1_5_4 = cert8_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_5_4 cert8_layer_1_5_4_eq 23

theorem cert8_step_1_5 :
    closedCollarIndexStepBool word fiber8 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_5)
    (by decide) (by decide)
    (by simpa [cert8_move_1_5] using cert8_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_1_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_1_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_1_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_1_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_9_0 = cert8_layer_1_9_0 := by
  decide

def cert8_seen_1_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_1_9_1 : List ChainEdge :=
  []

theorem cert8_layer_1_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_9_1 = cert8_layer_1_9_1 := by
  decide

theorem cert8_component_1_9_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_1_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 27 cert8_seen_1_9_0 = cert8_component_1_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_9_0 cert8_layer_1_9_0 26 cert8_layer_1_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 26 cert8_seen_1_9_1 = cert8_component_1_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_9_1 cert8_layer_1_9_1_eq 26

theorem cert8_step_1_9 :
    closedCollarIndexStepBool word fiber8 1 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_9)
    (by decide) (by decide)
    (by simpa [cert8_move_1_9] using cert8_component_1_9_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_1_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_1_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_17_0 = cert8_layer_1_17_0 := by
  decide

def cert8_seen_1_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_1_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_17_1 = cert8_layer_1_17_1 := by
  decide

def cert8_seen_1_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_1_17_2 : List ChainEdge :=
  []

theorem cert8_layer_1_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_17_2 = cert8_layer_1_17_2 := by
  decide

theorem cert8_component_1_17_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_1_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 27 cert8_seen_1_17_0 = cert8_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_17_0 cert8_layer_1_17_0 26 cert8_layer_1_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 26 cert8_seen_1_17_1 = cert8_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_17_1 cert8_layer_1_17_1 25 cert8_layer_1_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 25 cert8_seen_1_17_2 = cert8_component_1_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_17_2 cert8_layer_1_17_2_eq 25

theorem cert8_step_1_17 :
    closedCollarIndexStepBool word fiber8 1 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_17)
    (by decide) (by decide)
    (by simpa [cert8_move_1_17] using cert8_component_1_17_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_2_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_2_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_2_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_1_0 = cert8_layer_2_1_0 := by
  decide

def cert8_seen_2_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_2_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_2_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_1_1 = cert8_layer_2_1_1 := by
  decide

def cert8_seen_2_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_2_1_2 : List ChainEdge :=
  []

theorem cert8_layer_2_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_1_2 = cert8_layer_2_1_2 := by
  decide

theorem cert8_component_2_1_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_2_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 27 cert8_seen_2_1_0 = cert8_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_1_0 cert8_layer_2_1_0 26 cert8_layer_2_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 26 cert8_seen_2_1_1 = cert8_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_1_1 cert8_layer_2_1_1 25 cert8_layer_2_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 25 cert8_seen_2_1_2 = cert8_component_2_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_1_2 cert8_layer_2_1_2_eq 25

theorem cert8_step_2_1 :
    closedCollarIndexStepBool word fiber8 2 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_1)
    (by decide) (by decide)
    (by simpa [cert8_move_2_1] using cert8_component_2_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_2_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_2_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_2_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_2_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_10_0 = cert8_layer_2_10_0 := by
  decide

def cert8_seen_2_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_2_10_1 : List ChainEdge :=
  []

theorem cert8_layer_2_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_10_1 = cert8_layer_2_10_1 := by
  decide

theorem cert8_component_2_10_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_2_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 27 cert8_seen_2_10_0 = cert8_component_2_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_10_0 cert8_layer_2_10_0 26 cert8_layer_2_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 26 cert8_seen_2_10_1 = cert8_component_2_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_10_1 cert8_layer_2_10_1_eq 26

theorem cert8_step_2_10 :
    closedCollarIndexStepBool word fiber8 2 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_10)
    (by decide) (by decide)
    (by simpa [cert8_move_2_10] using cert8_component_2_10_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_2_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_2_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_18_0 = cert8_layer_2_18_0 := by
  decide

def cert8_seen_2_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_2_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_2_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_18_1 = cert8_layer_2_18_1 := by
  decide

def cert8_seen_2_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_2_18_2 : List ChainEdge :=
  []

theorem cert8_layer_2_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_18_2 = cert8_layer_2_18_2 := by
  decide

theorem cert8_component_2_18_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_2_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 27 cert8_seen_2_18_0 = cert8_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_18_0 cert8_layer_2_18_0 26 cert8_layer_2_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 26 cert8_seen_2_18_1 = cert8_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_18_1 cert8_layer_2_18_1 25 cert8_layer_2_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 25 cert8_seen_2_18_2 = cert8_component_2_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_18_2 cert8_layer_2_18_2_eq 25

theorem cert8_step_2_18 :
    closedCollarIndexStepBool word fiber8 2 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_18)
    (by decide) (by decide)
    (by simpa [cert8_move_2_18] using cert8_component_2_18_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_3_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_3_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_3_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_0_0 = cert8_layer_3_0_0 := by
  decide

def cert8_seen_3_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_3_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_3_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_0_1 = cert8_layer_3_0_1 := by
  decide

def cert8_seen_3_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_3_0_2 : List ChainEdge :=
  []

theorem cert8_layer_3_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_0_2 = cert8_layer_3_0_2 := by
  decide

theorem cert8_component_3_0_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_3_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 27 cert8_seen_3_0_0 = cert8_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_0_0 cert8_layer_3_0_0 26 cert8_layer_3_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 26 cert8_seen_3_0_1 = cert8_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_0_1 cert8_layer_3_0_1 25 cert8_layer_3_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 25 cert8_seen_3_0_2 = cert8_component_3_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_0_2 cert8_layer_3_0_2_eq 25

theorem cert8_step_3_0 :
    closedCollarIndexStepBool word fiber8 3 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_0)
    (by decide) (by decide)
    (by simpa [cert8_move_3_0] using cert8_component_3_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_3_7 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_3_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_3_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_3_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_7_0 = cert8_layer_3_7_0 := by
  decide

def cert8_seen_3_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_3_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_3_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_7_1 = cert8_layer_3_7_1 := by
  decide

def cert8_seen_3_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_3_7_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_3_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_7_2 = cert8_layer_3_7_2 := by
  decide

def cert8_seen_3_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_3_7_3 : List ChainEdge :=
  []

theorem cert8_layer_3_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_7_3 = cert8_layer_3_7_3 := by
  decide

theorem cert8_component_3_7_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_3_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 27 cert8_seen_3_7_0 = cert8_component_3_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_7_0 cert8_layer_3_7_0 26 cert8_layer_3_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 26 cert8_seen_3_7_1 = cert8_component_3_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_7_1 cert8_layer_3_7_1 25 cert8_layer_3_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 25 cert8_seen_3_7_2 = cert8_component_3_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_7_2 cert8_layer_3_7_2 24 cert8_layer_3_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 24 cert8_seen_3_7_3 = cert8_component_3_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_7_3 cert8_layer_3_7_3_eq 24

theorem cert8_step_3_7 :
    closedCollarIndexStepBool word fiber8 3 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_7)
    (by decide) (by decide)
    (by simpa [cert8_move_3_7] using cert8_component_3_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_3_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_3_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_3_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_3_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_11_0 = cert8_layer_3_11_0 := by
  decide

def cert8_seen_3_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_3_11_1 : List ChainEdge :=
  []

theorem cert8_layer_3_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_11_1 = cert8_layer_3_11_1 := by
  decide

theorem cert8_component_3_11_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_3_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 27 cert8_seen_3_11_0 = cert8_component_3_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_11_0 cert8_layer_3_11_0 26 cert8_layer_3_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 26 cert8_seen_3_11_1 = cert8_component_3_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_11_1 cert8_layer_3_11_1_eq 26

theorem cert8_step_3_11 :
    closedCollarIndexStepBool word fiber8 3 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_11)
    (by decide) (by decide)
    (by simpa [cert8_move_3_11] using cert8_component_3_11_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_3_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_3_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_19_0 = cert8_layer_3_19_0 := by
  decide

def cert8_seen_3_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_3_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_3_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_19_1 = cert8_layer_3_19_1 := by
  decide

def cert8_seen_3_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_3_19_2 : List ChainEdge :=
  []

theorem cert8_layer_3_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_19_2 = cert8_layer_3_19_2 := by
  decide

theorem cert8_component_3_19_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_3_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 27 cert8_seen_3_19_0 = cert8_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_19_0 cert8_layer_3_19_0 26 cert8_layer_3_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 26 cert8_seen_3_19_1 = cert8_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_19_1 cert8_layer_3_19_1 25 cert8_layer_3_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 25 cert8_seen_3_19_2 = cert8_component_3_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_19_2 cert8_layer_3_19_2_eq 25

theorem cert8_step_3_19 :
    closedCollarIndexStepBool word fiber8 3 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_19)
    (by decide) (by decide)
    (by simpa [cert8_move_3_19] using cert8_component_3_19_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_4_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_4_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_0_0 = cert8_layer_4_0_0 := by
  decide

def cert8_seen_4_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_4_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_0_1 = cert8_layer_4_0_1 := by
  decide

def cert8_seen_4_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_4_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_0_2 = cert8_layer_4_0_2 := by
  decide

def cert8_seen_4_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_4_0_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_0_3 = cert8_layer_4_0_3 := by
  decide

def cert8_seen_4_0_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_4_0_4 : List ChainEdge :=
  []

theorem cert8_layer_4_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_0_4 = cert8_layer_4_0_4 := by
  decide

theorem cert8_component_4_0_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 27 cert8_seen_4_0_0 = cert8_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_0_0 cert8_layer_4_0_0 26 cert8_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 26 cert8_seen_4_0_1 = cert8_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_0_1 cert8_layer_4_0_1 25 cert8_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 25 cert8_seen_4_0_2 = cert8_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_0_2 cert8_layer_4_0_2 24 cert8_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 24 cert8_seen_4_0_3 = cert8_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_0_3 cert8_layer_4_0_3 23 cert8_layer_4_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 23 cert8_seen_4_0_4 = cert8_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_0_4 cert8_layer_4_0_4_eq 23

theorem cert8_step_4_0 :
    closedCollarIndexStepBool word fiber8 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_0)
    (by decide) (by decide)
    (by simpa [cert8_move_4_0] using cert8_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_4_6 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_4_6_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_4_6_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_4_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_6_0 = cert8_layer_4_6_0 := by
  decide

def cert8_seen_4_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_4_6_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_6_1 = cert8_layer_4_6_1 := by
  decide

def cert8_seen_4_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_4_6_2 : List ChainEdge :=
  []

theorem cert8_layer_4_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_6_2 = cert8_layer_4_6_2 := by
  decide

theorem cert8_component_4_6_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_4_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 27 cert8_seen_4_6_0 = cert8_component_4_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_6_0 cert8_layer_4_6_0 26 cert8_layer_4_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 26 cert8_seen_4_6_1 = cert8_component_4_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_6_1 cert8_layer_4_6_1 25 cert8_layer_4_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 25 cert8_seen_4_6_2 = cert8_component_4_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_6_2 cert8_layer_4_6_2_eq 25

theorem cert8_step_4_6 :
    closedCollarIndexStepBool word fiber8 4 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_6)
    (by decide) (by decide)
    (by simpa [cert8_move_4_6] using cert8_component_4_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_12 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_4_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_4_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_4_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_4_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_12_0 = cert8_layer_4_12_0 := by
  decide

def cert8_seen_4_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_4_12_1 : List ChainEdge :=
  []

theorem cert8_layer_4_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_12_1 = cert8_layer_4_12_1 := by
  decide

theorem cert8_component_4_12_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_4_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 27 cert8_seen_4_12_0 = cert8_component_4_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_12_0 cert8_layer_4_12_0 26 cert8_layer_4_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 26 cert8_seen_4_12_1 = cert8_component_4_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_12_1 cert8_layer_4_12_1_eq 26

theorem cert8_step_4_12 :
    closedCollarIndexStepBool word fiber8 4 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_12)
    (by decide) (by decide)
    (by simpa [cert8_move_4_12] using cert8_component_4_12_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_4_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_4_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_4_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_4_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_20_0 = cert8_layer_4_20_0 := by
  decide

def cert8_seen_4_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_4_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_20_1 = cert8_layer_4_20_1 := by
  decide

def cert8_seen_4_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_4_20_2 : List ChainEdge :=
  []

theorem cert8_layer_4_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_20_2 = cert8_layer_4_20_2 := by
  decide

theorem cert8_component_4_20_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_4_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 27 cert8_seen_4_20_0 = cert8_component_4_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_20_0 cert8_layer_4_20_0 26 cert8_layer_4_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 26 cert8_seen_4_20_1 = cert8_component_4_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_20_1 cert8_layer_4_20_1 25 cert8_layer_4_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 25 cert8_seen_4_20_2 = cert8_component_4_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_20_2 cert8_layer_4_20_2_eq 25

theorem cert8_step_4_20 :
    closedCollarIndexStepBool word fiber8 4 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_20)
    (by decide) (by decide)
    (by simpa [cert8_move_4_20] using cert8_component_4_20_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_32 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_4_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_4_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_4_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_4_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_32_0 = cert8_layer_4_32_0 := by
  decide

def cert8_seen_4_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_4_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_4_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_32_1 = cert8_layer_4_32_1 := by
  decide

def cert8_seen_4_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_4_32_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_4_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_32_2 = cert8_layer_4_32_2 := by
  decide

def cert8_seen_4_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_4_32_3 : List ChainEdge :=
  []

theorem cert8_layer_4_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_32_3 = cert8_layer_4_32_3 := by
  decide

theorem cert8_component_4_32_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_4_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 27 cert8_seen_4_32_0 = cert8_component_4_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_32_0 cert8_layer_4_32_0 26 cert8_layer_4_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 26 cert8_seen_4_32_1 = cert8_component_4_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_32_1 cert8_layer_4_32_1 25 cert8_layer_4_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 25 cert8_seen_4_32_2 = cert8_component_4_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_32_2 cert8_layer_4_32_2 24 cert8_layer_4_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 24 cert8_seen_4_32_3 = cert8_component_4_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_32_3 cert8_layer_4_32_3_eq 24

theorem cert8_step_4_32 :
    closedCollarIndexStepBool word fiber8 4 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_32)
    (by decide) (by decide)
    (by simpa [cert8_move_4_32] using cert8_component_4_32_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_5_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_5_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_1_0 = cert8_layer_5_1_0 := by
  decide

def cert8_seen_5_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_5_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_1_1 = cert8_layer_5_1_1 := by
  decide

def cert8_seen_5_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_5_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_1_2 = cert8_layer_5_1_2 := by
  decide

def cert8_seen_5_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_5_1_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_1_3 = cert8_layer_5_1_3 := by
  decide

def cert8_seen_5_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_5_1_4 : List ChainEdge :=
  []

theorem cert8_layer_5_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_1_4 = cert8_layer_5_1_4 := by
  decide

theorem cert8_component_5_1_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 27 cert8_seen_5_1_0 = cert8_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_1_0 cert8_layer_5_1_0 26 cert8_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 26 cert8_seen_5_1_1 = cert8_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_1_1 cert8_layer_5_1_1 25 cert8_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 25 cert8_seen_5_1_2 = cert8_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_1_2 cert8_layer_5_1_2 24 cert8_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 24 cert8_seen_5_1_3 = cert8_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_1_3 cert8_layer_5_1_3 23 cert8_layer_5_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 23 cert8_seen_5_1_4 = cert8_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_1_4 cert8_layer_5_1_4_eq 23

theorem cert8_step_5_1 :
    closedCollarIndexStepBool word fiber8 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_1)
    (by decide) (by decide)
    (by simpa [cert8_move_5_1] using cert8_component_5_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_13 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_5_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_5_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_5_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_5_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_13_0 = cert8_layer_5_13_0 := by
  decide

def cert8_seen_5_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_5_13_1 : List ChainEdge :=
  []

theorem cert8_layer_5_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_13_1 = cert8_layer_5_13_1 := by
  decide

theorem cert8_component_5_13_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_5_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 27 cert8_seen_5_13_0 = cert8_component_5_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_13_0 cert8_layer_5_13_0 26 cert8_layer_5_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 26 cert8_seen_5_13_1 = cert8_component_5_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_13_1 cert8_layer_5_13_1_eq 26

theorem cert8_step_5_13 :
    closedCollarIndexStepBool word fiber8 5 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_13)
    (by decide) (by decide)
    (by simpa [cert8_move_5_13] using cert8_component_5_13_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_5_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_5_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_5_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_5_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_21_0 = cert8_layer_5_21_0 := by
  decide

def cert8_seen_5_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_5_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_5_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_21_1 = cert8_layer_5_21_1 := by
  decide

def cert8_seen_5_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_5_21_2 : List ChainEdge :=
  []

theorem cert8_layer_5_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_21_2 = cert8_layer_5_21_2 := by
  decide

theorem cert8_component_5_21_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_5_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 27 cert8_seen_5_21_0 = cert8_component_5_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_21_0 cert8_layer_5_21_0 26 cert8_layer_5_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 26 cert8_seen_5_21_1 = cert8_component_5_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_21_1 cert8_layer_5_21_1 25 cert8_layer_5_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 25 cert8_seen_5_21_2 = cert8_component_5_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_21_2 cert8_layer_5_21_2_eq 25

theorem cert8_step_5_21 :
    closedCollarIndexStepBool word fiber8 5 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_21)
    (by decide) (by decide)
    (by simpa [cert8_move_5_21] using cert8_component_5_21_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_33 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_5_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_5_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_5_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_5_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_33_0 = cert8_layer_5_33_0 := by
  decide

def cert8_seen_5_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_5_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_5_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_33_1 = cert8_layer_5_33_1 := by
  decide

def cert8_seen_5_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_5_33_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_5_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_33_2 = cert8_layer_5_33_2 := by
  decide

def cert8_seen_5_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_5_33_3 : List ChainEdge :=
  []

theorem cert8_layer_5_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_33_3 = cert8_layer_5_33_3 := by
  decide

theorem cert8_component_5_33_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_5_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 27 cert8_seen_5_33_0 = cert8_component_5_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_33_0 cert8_layer_5_33_0 26 cert8_layer_5_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 26 cert8_seen_5_33_1 = cert8_component_5_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_33_1 cert8_layer_5_33_1 25 cert8_layer_5_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 25 cert8_seen_5_33_2 = cert8_component_5_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_33_2 cert8_layer_5_33_2 24 cert8_layer_5_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 24 cert8_seen_5_33_3 = cert8_component_5_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_33_3 cert8_layer_5_33_3_eq 24

theorem cert8_step_5_33 :
    closedCollarIndexStepBool word fiber8 5 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_33)
    (by decide) (by decide)
    (by simpa [cert8_move_5_33] using cert8_component_5_33_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_6_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_seen_6_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_6_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_6_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_4_0 = cert8_layer_6_4_0 := by
  decide

def cert8_seen_6_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_6_4_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_6_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_4_1 = cert8_layer_6_4_1 := by
  decide

def cert8_seen_6_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_6_4_2 : List ChainEdge :=
  []

theorem cert8_layer_6_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_4_2 = cert8_layer_6_4_2 := by
  decide

theorem cert8_component_6_4_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert8_component_6_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 27 cert8_seen_6_4_0 = cert8_component_6_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_4_0 cert8_layer_6_4_0 26 cert8_layer_6_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 26 cert8_seen_6_4_1 = cert8_component_6_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_4_1 cert8_layer_6_4_1 25 cert8_layer_6_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 25 cert8_seen_6_4_2 = cert8_component_6_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_4_2 cert8_layer_6_4_2_eq 25

theorem cert8_step_6_4 :
    closedCollarIndexStepBool word fiber8 6 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_4)
    (by decide) (by decide)
    (by simpa [cert8_move_6_4] using cert8_component_6_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_14 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_6_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_6_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_14_0 = cert8_layer_6_14_0 := by
  decide

def cert8_seen_6_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_6_14_1 : List ChainEdge :=
  []

theorem cert8_layer_6_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_14_1 = cert8_layer_6_14_1 := by
  decide

theorem cert8_component_6_14_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_6_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 27 cert8_seen_6_14_0 = cert8_component_6_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_14_0 cert8_layer_6_14_0 26 cert8_layer_6_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 26 cert8_seen_6_14_1 = cert8_component_6_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_14_1 cert8_layer_6_14_1_eq 26

theorem cert8_step_6_14 :
    closedCollarIndexStepBool word fiber8 6 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_14)
    (by decide) (by decide)
    (by simpa [cert8_move_6_14] using cert8_component_6_14_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_6_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_6_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_6_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_6_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_22_0 = cert8_layer_6_22_0 := by
  decide

def cert8_seen_6_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_6_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_6_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_22_1 = cert8_layer_6_22_1 := by
  decide

def cert8_seen_6_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_6_22_2 : List ChainEdge :=
  []

theorem cert8_layer_6_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_22_2 = cert8_layer_6_22_2 := by
  decide

theorem cert8_component_6_22_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_6_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 27 cert8_seen_6_22_0 = cert8_component_6_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_22_0 cert8_layer_6_22_0 26 cert8_layer_6_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 26 cert8_seen_6_22_1 = cert8_component_6_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_22_1 cert8_layer_6_22_1 25 cert8_layer_6_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 25 cert8_seen_6_22_2 = cert8_component_6_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_22_2 cert8_layer_6_22_2_eq 25

theorem cert8_step_6_22 :
    closedCollarIndexStepBool word fiber8 6 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_22)
    (by decide) (by decide)
    (by simpa [cert8_move_6_22] using cert8_component_6_22_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_34 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_6_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_6_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_6_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_6_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_34_0 = cert8_layer_6_34_0 := by
  decide

def cert8_seen_6_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_6_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_6_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_34_1 = cert8_layer_6_34_1 := by
  decide

def cert8_seen_6_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_6_34_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_6_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_34_2 = cert8_layer_6_34_2 := by
  decide

def cert8_seen_6_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_6_34_3 : List ChainEdge :=
  []

theorem cert8_layer_6_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_34_3 = cert8_layer_6_34_3 := by
  decide

theorem cert8_component_6_34_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_6_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 27 cert8_seen_6_34_0 = cert8_component_6_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_34_0 cert8_layer_6_34_0 26 cert8_layer_6_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 26 cert8_seen_6_34_1 = cert8_component_6_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_34_1 cert8_layer_6_34_1 25 cert8_layer_6_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 25 cert8_seen_6_34_2 = cert8_component_6_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_34_2 cert8_layer_6_34_2 24 cert8_layer_6_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 24 cert8_seen_6_34_3 = cert8_component_6_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_34_3 cert8_layer_6_34_3_eq 24

theorem cert8_step_6_34 :
    closedCollarIndexStepBool word fiber8 6 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_34)
    (by decide) (by decide)
    (by simpa [cert8_move_6_34] using cert8_component_6_34_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_7_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_7_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_7_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_3_0 = cert8_layer_7_3_0 := by
  decide

def cert8_seen_7_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_7_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_7_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_3_1 = cert8_layer_7_3_1 := by
  decide

def cert8_seen_7_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_7_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_7_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_3_2 = cert8_layer_7_3_2 := by
  decide

def cert8_seen_7_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_7_3_3 : List ChainEdge :=
  []

theorem cert8_layer_7_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_3_3 = cert8_layer_7_3_3 := by
  decide

theorem cert8_component_7_3_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert8_component_7_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 27 cert8_seen_7_3_0 = cert8_component_7_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_3_0 cert8_layer_7_3_0 26 cert8_layer_7_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 26 cert8_seen_7_3_1 = cert8_component_7_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_3_1 cert8_layer_7_3_1 25 cert8_layer_7_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 25 cert8_seen_7_3_2 = cert8_component_7_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_3_2 cert8_layer_7_3_2 24 cert8_layer_7_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 24 cert8_seen_7_3_3 = cert8_component_7_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_3_3 cert8_layer_7_3_3_eq 24

theorem cert8_step_7_3 :
    closedCollarIndexStepBool word fiber8 7 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_3)
    (by decide) (by decide)
    (by simpa [cert8_move_7_3] using cert8_component_7_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_15 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_7_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_7_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_15_0 = cert8_layer_7_15_0 := by
  decide

def cert8_seen_7_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_7_15_1 : List ChainEdge :=
  []

theorem cert8_layer_7_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_15_1 = cert8_layer_7_15_1 := by
  decide

theorem cert8_component_7_15_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_7_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 27 cert8_seen_7_15_0 = cert8_component_7_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_15_0 cert8_layer_7_15_0 26 cert8_layer_7_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 26 cert8_seen_7_15_1 = cert8_component_7_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_15_1 cert8_layer_7_15_1_eq 26

theorem cert8_step_7_15 :
    closedCollarIndexStepBool word fiber8 7 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_15)
    (by decide) (by decide)
    (by simpa [cert8_move_7_15] using cert8_component_7_15_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_7_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_7_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_7_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_7_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_23_0 = cert8_layer_7_23_0 := by
  decide

def cert8_seen_7_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_7_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_7_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_23_1 = cert8_layer_7_23_1 := by
  decide

def cert8_seen_7_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_7_23_2 : List ChainEdge :=
  []

theorem cert8_layer_7_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_23_2 = cert8_layer_7_23_2 := by
  decide

theorem cert8_component_7_23_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_7_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 27 cert8_seen_7_23_0 = cert8_component_7_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_23_0 cert8_layer_7_23_0 26 cert8_layer_7_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 26 cert8_seen_7_23_1 = cert8_component_7_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_23_1 cert8_layer_7_23_1 25 cert8_layer_7_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 25 cert8_seen_7_23_2 = cert8_component_7_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_23_2 cert8_layer_7_23_2_eq 25

theorem cert8_step_7_23 :
    closedCollarIndexStepBool word fiber8 7 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_23)
    (by decide) (by decide)
    (by simpa [cert8_move_7_23] using cert8_component_7_23_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_35 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_7_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_7_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_7_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_7_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_35_0 = cert8_layer_7_35_0 := by
  decide

def cert8_seen_7_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_7_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_7_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_35_1 = cert8_layer_7_35_1 := by
  decide

def cert8_seen_7_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_7_35_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_7_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_35_2 = cert8_layer_7_35_2 := by
  decide

def cert8_seen_7_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_7_35_3 : List ChainEdge :=
  []

theorem cert8_layer_7_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_35_3 = cert8_layer_7_35_3 := by
  decide

theorem cert8_component_7_35_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_7_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 27 cert8_seen_7_35_0 = cert8_component_7_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_35_0 cert8_layer_7_35_0 26 cert8_layer_7_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 26 cert8_seen_7_35_1 = cert8_component_7_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_35_1 cert8_layer_7_35_1 25 cert8_layer_7_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 25 cert8_seen_7_35_2 = cert8_component_7_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_35_2 cert8_layer_7_35_2 24 cert8_layer_7_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 24 cert8_seen_7_35_3 = cert8_component_7_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_35_3 cert8_layer_7_35_3_eq 24

theorem cert8_step_7_35 :
    closedCollarIndexStepBool word fiber8 7 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_35)
    (by decide) (by decide)
    (by simpa [cert8_move_7_35] using cert8_component_7_35_eq)
    (by decide) (by decide) (by decide)

def cert8_move_8_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_8_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_8_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_8_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.b LColor.p cert8_seen_8_0_0 = cert8_layer_8_0_0 := by
  decide

def cert8_seen_8_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_8_0_1 : List ChainEdge :=
  []

theorem cert8_layer_8_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.b LColor.p cert8_seen_8_0_1 = cert8_layer_8_0_1 := by
  decide

theorem cert8_component_8_0_eq :
    closedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_8_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p 27 cert8_seen_8_0_0 = cert8_component_8_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.b LColor.p
    cert8_seen_8_0_0 cert8_layer_8_0_0 26 cert8_layer_8_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p 26 cert8_seen_8_0_1 = cert8_component_8_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 8 []) LColor.b LColor.p
    cert8_seen_8_0_1 cert8_layer_8_0_1_eq 26

theorem cert8_step_8_0 :
    closedCollarIndexStepBool word fiber8 8 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_8_0)
    (by decide) (by decide)
    (by simpa [cert8_move_8_0] using cert8_component_8_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_8_24 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_8_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_8_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_8_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_8_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_24_0 = cert8_layer_8_24_0 := by
  decide

def cert8_seen_8_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_8_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_8_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_24_1 = cert8_layer_8_24_1 := by
  decide

def cert8_seen_8_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_8_24_2 : List ChainEdge :=
  []

theorem cert8_layer_8_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_24_2 = cert8_layer_8_24_2 := by
  decide

theorem cert8_component_8_24_eq :
    closedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_8_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 27 cert8_seen_8_24_0 = cert8_component_8_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_24_0 cert8_layer_8_24_0 26 cert8_layer_8_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 26 cert8_seen_8_24_1 = cert8_component_8_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_24_1 cert8_layer_8_24_1 25 cert8_layer_8_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 25 cert8_seen_8_24_2 = cert8_component_8_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_24_2 cert8_layer_8_24_2_eq 25

theorem cert8_step_8_24 :
    closedCollarIndexStepBool word fiber8 8 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_8_24)
    (by decide) (by decide)
    (by simpa [cert8_move_8_24] using cert8_component_8_24_eq)
    (by decide) (by decide) (by decide)

def cert8_move_9_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_9_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_9_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_9_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.b LColor.p cert8_seen_9_1_0 = cert8_layer_9_1_0 := by
  decide

def cert8_seen_9_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_9_1_1 : List ChainEdge :=
  []

theorem cert8_layer_9_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.b LColor.p cert8_seen_9_1_1 = cert8_layer_9_1_1 := by
  decide

theorem cert8_component_9_1_eq :
    closedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_9_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p 27 cert8_seen_9_1_0 = cert8_component_9_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.b LColor.p
    cert8_seen_9_1_0 cert8_layer_9_1_0 26 cert8_layer_9_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p 26 cert8_seen_9_1_1 = cert8_component_9_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 9 []) LColor.b LColor.p
    cert8_seen_9_1_1 cert8_layer_9_1_1_eq 26

theorem cert8_step_9_1 :
    closedCollarIndexStepBool word fiber8 9 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_9_1)
    (by decide) (by decide)
    (by simpa [cert8_move_9_1] using cert8_component_9_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_9_25 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_9_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_9_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_9_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_9_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_25_0 = cert8_layer_9_25_0 := by
  decide

def cert8_seen_9_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_9_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_9_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_25_1 = cert8_layer_9_25_1 := by
  decide

def cert8_seen_9_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_9_25_2 : List ChainEdge :=
  []

theorem cert8_layer_9_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_25_2 = cert8_layer_9_25_2 := by
  decide

theorem cert8_component_9_25_eq :
    closedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_9_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 27 cert8_seen_9_25_0 = cert8_component_9_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_25_0 cert8_layer_9_25_0 26 cert8_layer_9_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 26 cert8_seen_9_25_1 = cert8_component_9_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_25_1 cert8_layer_9_25_1 25 cert8_layer_9_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 25 cert8_seen_9_25_2 = cert8_component_9_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_25_2 cert8_layer_9_25_2_eq 25

theorem cert8_step_9_25 :
    closedCollarIndexStepBool word fiber8 9 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_9_25)
    (by decide) (by decide)
    (by simpa [cert8_move_9_25] using cert8_component_9_25_eq)
    (by decide) (by decide) (by decide)

def cert8_move_10_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_10_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_10_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_10_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.b LColor.p cert8_seen_10_2_0 = cert8_layer_10_2_0 := by
  decide

def cert8_seen_10_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_10_2_1 : List ChainEdge :=
  []

theorem cert8_layer_10_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.b LColor.p cert8_seen_10_2_1 = cert8_layer_10_2_1 := by
  decide

theorem cert8_component_10_2_eq :
    closedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_10_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p 27 cert8_seen_10_2_0 = cert8_component_10_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.b LColor.p
    cert8_seen_10_2_0 cert8_layer_10_2_0 26 cert8_layer_10_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p 26 cert8_seen_10_2_1 = cert8_component_10_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 10 []) LColor.b LColor.p
    cert8_seen_10_2_1 cert8_layer_10_2_1_eq 26

theorem cert8_step_10_2 :
    closedCollarIndexStepBool word fiber8 10 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_10_2)
    (by decide) (by decide)
    (by simpa [cert8_move_10_2] using cert8_component_10_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_10_26 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_10_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_10_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_10_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_10_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_26_0 = cert8_layer_10_26_0 := by
  decide

def cert8_seen_10_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_10_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_10_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_26_1 = cert8_layer_10_26_1 := by
  decide

def cert8_seen_10_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_10_26_2 : List ChainEdge :=
  []

theorem cert8_layer_10_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_26_2 = cert8_layer_10_26_2 := by
  decide

theorem cert8_component_10_26_eq :
    closedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_10_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 27 cert8_seen_10_26_0 = cert8_component_10_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_26_0 cert8_layer_10_26_0 26 cert8_layer_10_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 26 cert8_seen_10_26_1 = cert8_component_10_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_26_1 cert8_layer_10_26_1 25 cert8_layer_10_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 25 cert8_seen_10_26_2 = cert8_component_10_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_26_2 cert8_layer_10_26_2_eq 25

theorem cert8_step_10_26 :
    closedCollarIndexStepBool word fiber8 10 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_10_26)
    (by decide) (by decide)
    (by simpa [cert8_move_10_26] using cert8_component_10_26_eq)
    (by decide) (by decide) (by decide)

def cert8_move_11_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_11_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_11_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_11_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.b LColor.p cert8_seen_11_3_0 = cert8_layer_11_3_0 := by
  decide

def cert8_seen_11_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_11_3_1 : List ChainEdge :=
  []

theorem cert8_layer_11_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.b LColor.p cert8_seen_11_3_1 = cert8_layer_11_3_1 := by
  decide

theorem cert8_component_11_3_eq :
    closedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_11_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p 27 cert8_seen_11_3_0 = cert8_component_11_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.b LColor.p
    cert8_seen_11_3_0 cert8_layer_11_3_0 26 cert8_layer_11_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p 26 cert8_seen_11_3_1 = cert8_component_11_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 11 []) LColor.b LColor.p
    cert8_seen_11_3_1 cert8_layer_11_3_1_eq 26

theorem cert8_step_11_3 :
    closedCollarIndexStepBool word fiber8 11 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_11_3)
    (by decide) (by decide)
    (by simpa [cert8_move_11_3] using cert8_component_11_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_11_27 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_11_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_11_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_11_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_11_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_27_0 = cert8_layer_11_27_0 := by
  decide

def cert8_seen_11_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_11_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_11_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_27_1 = cert8_layer_11_27_1 := by
  decide

def cert8_seen_11_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_11_27_2 : List ChainEdge :=
  []

theorem cert8_layer_11_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_27_2 = cert8_layer_11_27_2 := by
  decide

theorem cert8_component_11_27_eq :
    closedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_11_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 27 cert8_seen_11_27_0 = cert8_component_11_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_27_0 cert8_layer_11_27_0 26 cert8_layer_11_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 26 cert8_seen_11_27_1 = cert8_component_11_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_27_1 cert8_layer_11_27_1 25 cert8_layer_11_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 25 cert8_seen_11_27_2 = cert8_component_11_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_27_2 cert8_layer_11_27_2_eq 25

theorem cert8_step_11_27 :
    closedCollarIndexStepBool word fiber8 11 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_11_27)
    (by decide) (by decide)
    (by simpa [cert8_move_11_27] using cert8_component_11_27_eq)
    (by decide) (by decide) (by decide)

def cert8_move_12_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_12_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_12_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_12_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_12_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_4_0 = cert8_layer_12_4_0 := by
  decide

def cert8_seen_12_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_12_4_1 : List ChainEdge :=
  []

theorem cert8_layer_12_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_4_1 = cert8_layer_12_4_1 := by
  decide

theorem cert8_component_12_4_eq :
    closedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_12_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 27 cert8_seen_12_4_0 = cert8_component_12_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_4_0 cert8_layer_12_4_0 26 cert8_layer_12_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 26 cert8_seen_12_4_1 = cert8_component_12_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_4_1 cert8_layer_12_4_1_eq 26

theorem cert8_step_12_4 :
    closedCollarIndexStepBool word fiber8 12 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_12_4)
    (by decide) (by decide)
    (by simpa [cert8_move_12_4] using cert8_component_12_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_12_28 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_12_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_12_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_12_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_12_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.b cert8_seen_12_28_0 = cert8_layer_12_28_0 := by
  decide

def cert8_seen_12_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_12_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_12_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.b cert8_seen_12_28_1 = cert8_layer_12_28_1 := by
  decide

def cert8_seen_12_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_12_28_2 : List ChainEdge :=
  []

theorem cert8_layer_12_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.b cert8_seen_12_28_2 = cert8_layer_12_28_2 := by
  decide

theorem cert8_component_12_28_eq :
    closedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_12_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.b 27 cert8_seen_12_28_0 = cert8_component_12_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.r LColor.b
    cert8_seen_12_28_0 cert8_layer_12_28_0 26 cert8_layer_12_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.b 26 cert8_seen_12_28_1 = cert8_component_12_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.r LColor.b
    cert8_seen_12_28_1 cert8_layer_12_28_1 25 cert8_layer_12_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.b 25 cert8_seen_12_28_2 = cert8_component_12_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 12 []) LColor.r LColor.b
    cert8_seen_12_28_2 cert8_layer_12_28_2_eq 25

theorem cert8_step_12_28 :
    closedCollarIndexStepBool word fiber8 12 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_12_28)
    (by decide) (by decide)
    (by simpa [cert8_move_12_28] using cert8_component_12_28_eq)
    (by decide) (by decide) (by decide)

def cert8_move_12_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_12_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_12_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_36_0 = cert8_layer_12_36_0 := by
  decide

def cert8_seen_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_12_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_36_1 = cert8_layer_12_36_1 := by
  decide

def cert8_seen_12_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_12_36_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_12_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_36_2 = cert8_layer_12_36_2 := by
  decide

def cert8_seen_12_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_12_36_3 : List ChainEdge :=
  []

theorem cert8_layer_12_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.b LColor.p cert8_seen_12_36_3 = cert8_layer_12_36_3 := by
  decide

theorem cert8_component_12_36_eq :
    closedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_12_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 27 cert8_seen_12_36_0 = cert8_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_36_0 cert8_layer_12_36_0 26 cert8_layer_12_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 26 cert8_seen_12_36_1 = cert8_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_36_1 cert8_layer_12_36_1 25 cert8_layer_12_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 25 cert8_seen_12_36_2 = cert8_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_36_2 cert8_layer_12_36_2 24 cert8_layer_12_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.b LColor.p 24 cert8_seen_12_36_3 = cert8_component_12_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 12 []) LColor.b LColor.p
    cert8_seen_12_36_3 cert8_layer_12_36_3_eq 24

theorem cert8_step_12_36 :
    closedCollarIndexStepBool word fiber8 12 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_12_36)
    (by decide) (by decide)
    (by simpa [cert8_move_12_36] using cert8_component_12_36_eq)
    (by decide) (by decide) (by decide)

def cert8_move_13_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_13_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_13_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_13_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_13_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_5_0 = cert8_layer_13_5_0 := by
  decide

def cert8_seen_13_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_13_5_1 : List ChainEdge :=
  []

theorem cert8_layer_13_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_5_1 = cert8_layer_13_5_1 := by
  decide

theorem cert8_component_13_5_eq :
    closedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_13_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 27 cert8_seen_13_5_0 = cert8_component_13_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_5_0 cert8_layer_13_5_0 26 cert8_layer_13_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 26 cert8_seen_13_5_1 = cert8_component_13_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_5_1 cert8_layer_13_5_1_eq 26

theorem cert8_step_13_5 :
    closedCollarIndexStepBool word fiber8 13 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_13_5)
    (by decide) (by decide)
    (by simpa [cert8_move_13_5] using cert8_component_13_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_13_29 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_13_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_13_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_13_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_13_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.b cert8_seen_13_29_0 = cert8_layer_13_29_0 := by
  decide

def cert8_seen_13_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_13_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_13_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.b cert8_seen_13_29_1 = cert8_layer_13_29_1 := by
  decide

def cert8_seen_13_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_13_29_2 : List ChainEdge :=
  []

theorem cert8_layer_13_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.b cert8_seen_13_29_2 = cert8_layer_13_29_2 := by
  decide

theorem cert8_component_13_29_eq :
    closedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_13_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.b 27 cert8_seen_13_29_0 = cert8_component_13_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.r LColor.b
    cert8_seen_13_29_0 cert8_layer_13_29_0 26 cert8_layer_13_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.b 26 cert8_seen_13_29_1 = cert8_component_13_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.r LColor.b
    cert8_seen_13_29_1 cert8_layer_13_29_1 25 cert8_layer_13_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.b 25 cert8_seen_13_29_2 = cert8_component_13_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 13 []) LColor.r LColor.b
    cert8_seen_13_29_2 cert8_layer_13_29_2_eq 25

theorem cert8_step_13_29 :
    closedCollarIndexStepBool word fiber8 13 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_13_29)
    (by decide) (by decide)
    (by simpa [cert8_move_13_29] using cert8_component_13_29_eq)
    (by decide) (by decide) (by decide)

def cert8_move_13_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_13_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_13_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_37_0 = cert8_layer_13_37_0 := by
  decide

def cert8_seen_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_13_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_37_1 = cert8_layer_13_37_1 := by
  decide

def cert8_seen_13_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_13_37_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_13_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_37_2 = cert8_layer_13_37_2 := by
  decide

def cert8_seen_13_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_13_37_3 : List ChainEdge :=
  []

theorem cert8_layer_13_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.b LColor.p cert8_seen_13_37_3 = cert8_layer_13_37_3 := by
  decide

theorem cert8_component_13_37_eq :
    closedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_13_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 27 cert8_seen_13_37_0 = cert8_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_37_0 cert8_layer_13_37_0 26 cert8_layer_13_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 26 cert8_seen_13_37_1 = cert8_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_37_1 cert8_layer_13_37_1 25 cert8_layer_13_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 25 cert8_seen_13_37_2 = cert8_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_37_2 cert8_layer_13_37_2 24 cert8_layer_13_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.b LColor.p 24 cert8_seen_13_37_3 = cert8_component_13_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 13 []) LColor.b LColor.p
    cert8_seen_13_37_3 cert8_layer_13_37_3_eq 24

theorem cert8_step_13_37 :
    closedCollarIndexStepBool word fiber8 13 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_13_37)
    (by decide) (by decide)
    (by simpa [cert8_move_13_37] using cert8_component_13_37_eq)
    (by decide) (by decide) (by decide)

def cert8_move_14_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_14_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_14_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_6_0 = cert8_layer_14_6_0 := by
  decide

def cert8_seen_14_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_14_6_1 : List ChainEdge :=
  []

theorem cert8_layer_14_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_6_1 = cert8_layer_14_6_1 := by
  decide

theorem cert8_component_14_6_eq :
    closedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_14_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 27 cert8_seen_14_6_0 = cert8_component_14_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_6_0 cert8_layer_14_6_0 26 cert8_layer_14_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 26 cert8_seen_14_6_1 = cert8_component_14_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_6_1 cert8_layer_14_6_1_eq 26

theorem cert8_step_14_6 :
    closedCollarIndexStepBool word fiber8 14 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_14_6)
    (by decide) (by decide)
    (by simpa [cert8_move_14_6] using cert8_component_14_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_14_30 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_14_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_14_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_14_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_14_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.b cert8_seen_14_30_0 = cert8_layer_14_30_0 := by
  decide

def cert8_seen_14_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_14_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_14_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.b cert8_seen_14_30_1 = cert8_layer_14_30_1 := by
  decide

def cert8_seen_14_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_14_30_2 : List ChainEdge :=
  []

theorem cert8_layer_14_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.b cert8_seen_14_30_2 = cert8_layer_14_30_2 := by
  decide

theorem cert8_component_14_30_eq :
    closedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_14_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.b 27 cert8_seen_14_30_0 = cert8_component_14_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.r LColor.b
    cert8_seen_14_30_0 cert8_layer_14_30_0 26 cert8_layer_14_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.b 26 cert8_seen_14_30_1 = cert8_component_14_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.r LColor.b
    cert8_seen_14_30_1 cert8_layer_14_30_1 25 cert8_layer_14_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.b 25 cert8_seen_14_30_2 = cert8_component_14_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 14 []) LColor.r LColor.b
    cert8_seen_14_30_2 cert8_layer_14_30_2_eq 25

theorem cert8_step_14_30 :
    closedCollarIndexStepBool word fiber8 14 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_14_30)
    (by decide) (by decide)
    (by simpa [cert8_move_14_30] using cert8_component_14_30_eq)
    (by decide) (by decide) (by decide)

def cert8_move_14_38 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_14_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_14_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_38_0 = cert8_layer_14_38_0 := by
  decide

def cert8_seen_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_14_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_38_1 = cert8_layer_14_38_1 := by
  decide

def cert8_seen_14_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_14_38_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_14_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_38_2 = cert8_layer_14_38_2 := by
  decide

def cert8_seen_14_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_14_38_3 : List ChainEdge :=
  []

theorem cert8_layer_14_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.b LColor.p cert8_seen_14_38_3 = cert8_layer_14_38_3 := by
  decide

theorem cert8_component_14_38_eq :
    closedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_14_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 27 cert8_seen_14_38_0 = cert8_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_38_0 cert8_layer_14_38_0 26 cert8_layer_14_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 26 cert8_seen_14_38_1 = cert8_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_38_1 cert8_layer_14_38_1 25 cert8_layer_14_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 25 cert8_seen_14_38_2 = cert8_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_38_2 cert8_layer_14_38_2 24 cert8_layer_14_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.b LColor.p 24 cert8_seen_14_38_3 = cert8_component_14_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 14 []) LColor.b LColor.p
    cert8_seen_14_38_3 cert8_layer_14_38_3_eq 24

theorem cert8_step_14_38 :
    closedCollarIndexStepBool word fiber8 14 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_14_38)
    (by decide) (by decide)
    (by simpa [cert8_move_14_38] using cert8_component_14_38_eq)
    (by decide) (by decide) (by decide)

def cert8_move_15_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert8_component_15_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_seen_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert8_layer_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert8_layer_15_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_7_0 = cert8_layer_15_7_0 := by
  decide

def cert8_seen_15_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert8_layer_15_7_1 : List ChainEdge :=
  []

theorem cert8_layer_15_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_7_1 = cert8_layer_15_7_1 := by
  decide

theorem cert8_component_15_7_eq :
    closedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert8_component_15_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 27 cert8_seen_15_7_0 = cert8_component_15_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_7_0 cert8_layer_15_7_0 26 cert8_layer_15_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 26 cert8_seen_15_7_1 = cert8_component_15_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_7_1 cert8_layer_15_7_1_eq 26

theorem cert8_step_15_7 :
    closedCollarIndexStepBool word fiber8 15 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_15_7)
    (by decide) (by decide)
    (by simpa [cert8_move_15_7] using cert8_component_15_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_15_31 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_15_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_15_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_15_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_15_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.b cert8_seen_15_31_0 = cert8_layer_15_31_0 := by
  decide

def cert8_seen_15_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_15_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_15_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.b cert8_seen_15_31_1 = cert8_layer_15_31_1 := by
  decide

def cert8_seen_15_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_15_31_2 : List ChainEdge :=
  []

theorem cert8_layer_15_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.b cert8_seen_15_31_2 = cert8_layer_15_31_2 := by
  decide

theorem cert8_component_15_31_eq :
    closedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_15_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.b 27 cert8_seen_15_31_0 = cert8_component_15_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.r LColor.b
    cert8_seen_15_31_0 cert8_layer_15_31_0 26 cert8_layer_15_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.b 26 cert8_seen_15_31_1 = cert8_component_15_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.r LColor.b
    cert8_seen_15_31_1 cert8_layer_15_31_1 25 cert8_layer_15_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.b 25 cert8_seen_15_31_2 = cert8_component_15_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 15 []) LColor.r LColor.b
    cert8_seen_15_31_2 cert8_layer_15_31_2_eq 25

theorem cert8_step_15_31 :
    closedCollarIndexStepBool word fiber8 15 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_15_31)
    (by decide) (by decide)
    (by simpa [cert8_move_15_31] using cert8_component_15_31_eq)
    (by decide) (by decide) (by decide)

def cert8_move_15_39 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_15_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_15_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_39_0 = cert8_layer_15_39_0 := by
  decide

def cert8_seen_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_15_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_39_1 = cert8_layer_15_39_1 := by
  decide

def cert8_seen_15_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_15_39_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_15_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_39_2 = cert8_layer_15_39_2 := by
  decide

def cert8_seen_15_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_15_39_3 : List ChainEdge :=
  []

theorem cert8_layer_15_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.b LColor.p cert8_seen_15_39_3 = cert8_layer_15_39_3 := by
  decide

theorem cert8_component_15_39_eq :
    closedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_15_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 27 cert8_seen_15_39_0 = cert8_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_39_0 cert8_layer_15_39_0 26 cert8_layer_15_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 26 cert8_seen_15_39_1 = cert8_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_39_1 cert8_layer_15_39_1 25 cert8_layer_15_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 25 cert8_seen_15_39_2 = cert8_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_39_2 cert8_layer_15_39_2 24 cert8_layer_15_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.b LColor.p 24 cert8_seen_15_39_3 = cert8_component_15_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 15 []) LColor.b LColor.p
    cert8_seen_15_39_3 cert8_layer_15_39_3_eq 24

theorem cert8_step_15_39 :
    closedCollarIndexStepBool word fiber8 15 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_15_39)
    (by decide) (by decide)
    (by simpa [cert8_move_15_39] using cert8_component_15_39_eq)
    (by decide) (by decide) (by decide)

def cert8_move_16_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_16_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.b cert8_seen_16_0_0 = cert8_layer_16_0_0 := by
  decide

def cert8_seen_16_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_16_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_16_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.b cert8_seen_16_0_1 = cert8_layer_16_0_1 := by
  decide

def cert8_seen_16_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_16_0_2 : List ChainEdge :=
  []

theorem cert8_layer_16_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.b cert8_seen_16_0_2 = cert8_layer_16_0_2 := by
  decide

theorem cert8_component_16_0_eq :
    closedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_16_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.b 27 cert8_seen_16_0_0 = cert8_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 16 []) LColor.r LColor.b
    cert8_seen_16_0_0 cert8_layer_16_0_0 26 cert8_layer_16_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.b 26 cert8_seen_16_0_1 = cert8_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 16 []) LColor.r LColor.b
    cert8_seen_16_0_1 cert8_layer_16_0_1 25 cert8_layer_16_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.b 25 cert8_seen_16_0_2 = cert8_component_16_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 16 []) LColor.r LColor.b
    cert8_seen_16_0_2 cert8_layer_16_0_2_eq 25

theorem cert8_step_16_0 :
    closedCollarIndexStepBool word fiber8 16 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_16_0)
    (by decide) (by decide)
    (by simpa [cert8_move_16_0] using cert8_component_16_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_17_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_17_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.b cert8_seen_17_1_0 = cert8_layer_17_1_0 := by
  decide

def cert8_seen_17_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_17_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_17_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.b cert8_seen_17_1_1 = cert8_layer_17_1_1 := by
  decide

def cert8_seen_17_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_17_1_2 : List ChainEdge :=
  []

theorem cert8_layer_17_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.b cert8_seen_17_1_2 = cert8_layer_17_1_2 := by
  decide

theorem cert8_component_17_1_eq :
    closedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_17_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.b 27 cert8_seen_17_1_0 = cert8_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 17 []) LColor.r LColor.b
    cert8_seen_17_1_0 cert8_layer_17_1_0 26 cert8_layer_17_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.b 26 cert8_seen_17_1_1 = cert8_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 17 []) LColor.r LColor.b
    cert8_seen_17_1_1 cert8_layer_17_1_1 25 cert8_layer_17_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.b 25 cert8_seen_17_1_2 = cert8_component_17_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 17 []) LColor.r LColor.b
    cert8_seen_17_1_2 cert8_layer_17_1_2_eq 25

theorem cert8_step_17_1 :
    closedCollarIndexStepBool word fiber8 17 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_17_1)
    (by decide) (by decide)
    (by simpa [cert8_move_17_1] using cert8_component_17_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_18_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_18_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_2_0 = cert8_layer_18_2_0 := by
  decide

def cert8_seen_18_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_18_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_18_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_2_1 = cert8_layer_18_2_1 := by
  decide

def cert8_seen_18_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_18_2_2 : List ChainEdge :=
  []

theorem cert8_layer_18_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_2_2 = cert8_layer_18_2_2 := by
  decide

theorem cert8_component_18_2_eq :
    closedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_18_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 27 cert8_seen_18_2_0 = cert8_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_2_0 cert8_layer_18_2_0 26 cert8_layer_18_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 26 cert8_seen_18_2_1 = cert8_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_2_1 cert8_layer_18_2_1 25 cert8_layer_18_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 25 cert8_seen_18_2_2 = cert8_component_18_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_2_2 cert8_layer_18_2_2_eq 25

theorem cert8_step_18_2 :
    closedCollarIndexStepBool word fiber8 18 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_18_2)
    (by decide) (by decide)
    (by simpa [cert8_move_18_2] using cert8_component_18_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_19_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_19_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_3_0 = cert8_layer_19_3_0 := by
  decide

def cert8_seen_19_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_19_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_19_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_3_1 = cert8_layer_19_3_1 := by
  decide

def cert8_seen_19_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_19_3_2 : List ChainEdge :=
  []

theorem cert8_layer_19_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_3_2 = cert8_layer_19_3_2 := by
  decide

theorem cert8_component_19_3_eq :
    closedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_19_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 27 cert8_seen_19_3_0 = cert8_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_3_0 cert8_layer_19_3_0 26 cert8_layer_19_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 26 cert8_seen_19_3_1 = cert8_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_3_1 cert8_layer_19_3_1 25 cert8_layer_19_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 25 cert8_seen_19_3_2 = cert8_component_19_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_3_2 cert8_layer_19_3_2_eq 25

theorem cert8_step_19_3 :
    closedCollarIndexStepBool word fiber8 19 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_19_3)
    (by decide) (by decide)
    (by simpa [cert8_move_19_3] using cert8_component_19_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_20_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_20_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_20_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_20_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_20_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_4_0 = cert8_layer_20_4_0 := by
  decide

def cert8_seen_20_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_20_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_20_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_4_1 = cert8_layer_20_4_1 := by
  decide

def cert8_seen_20_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_20_4_2 : List ChainEdge :=
  []

theorem cert8_layer_20_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_4_2 = cert8_layer_20_4_2 := by
  decide

theorem cert8_component_20_4_eq :
    closedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_20_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 27 cert8_seen_20_4_0 = cert8_component_20_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_4_0 cert8_layer_20_4_0 26 cert8_layer_20_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 26 cert8_seen_20_4_1 = cert8_component_20_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_4_1 cert8_layer_20_4_1 25 cert8_layer_20_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 25 cert8_seen_20_4_2 = cert8_component_20_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_4_2 cert8_layer_20_4_2_eq 25

theorem cert8_step_20_4 :
    closedCollarIndexStepBool word fiber8 20 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_20_4)
    (by decide) (by decide)
    (by simpa [cert8_move_20_4] using cert8_component_20_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_20_40 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_20_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_20_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_20_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_20_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.b LColor.p cert8_seen_20_40_0 = cert8_layer_20_40_0 := by
  decide

def cert8_seen_20_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_20_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_20_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.b LColor.p cert8_seen_20_40_1 = cert8_layer_20_40_1 := by
  decide

def cert8_seen_20_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_20_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_20_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.b LColor.p cert8_seen_20_40_2 = cert8_layer_20_40_2 := by
  decide

def cert8_seen_20_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_20_40_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_20_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.b LColor.p cert8_seen_20_40_3 = cert8_layer_20_40_3 := by
  decide

def cert8_seen_20_40_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_20_40_4 : List ChainEdge :=
  []

theorem cert8_layer_20_40_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.b LColor.p cert8_seen_20_40_4 = cert8_layer_20_40_4 := by
  decide

theorem cert8_component_20_40_eq :
    closedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_20_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p 27 cert8_seen_20_40_0 = cert8_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.b LColor.p
    cert8_seen_20_40_0 cert8_layer_20_40_0 26 cert8_layer_20_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p 26 cert8_seen_20_40_1 = cert8_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.b LColor.p
    cert8_seen_20_40_1 cert8_layer_20_40_1 25 cert8_layer_20_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p 25 cert8_seen_20_40_2 = cert8_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.b LColor.p
    cert8_seen_20_40_2 cert8_layer_20_40_2 24 cert8_layer_20_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p 24 cert8_seen_20_40_3 = cert8_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.b LColor.p
    cert8_seen_20_40_3 cert8_layer_20_40_3 23 cert8_layer_20_40_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.b LColor.p 23 cert8_seen_20_40_4 = cert8_component_20_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 20 []) LColor.b LColor.p
    cert8_seen_20_40_4 cert8_layer_20_40_4_eq 23

theorem cert8_step_20_40 :
    closedCollarIndexStepBool word fiber8 20 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_20_40)
    (by decide) (by decide)
    (by simpa [cert8_move_20_40] using cert8_component_20_40_eq)
    (by decide) (by decide) (by decide)

def cert8_move_21_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_21_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_21_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_21_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_21_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_5_0 = cert8_layer_21_5_0 := by
  decide

def cert8_seen_21_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_21_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_21_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_5_1 = cert8_layer_21_5_1 := by
  decide

def cert8_seen_21_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_21_5_2 : List ChainEdge :=
  []

theorem cert8_layer_21_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_5_2 = cert8_layer_21_5_2 := by
  decide

theorem cert8_component_21_5_eq :
    closedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_21_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 27 cert8_seen_21_5_0 = cert8_component_21_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_5_0 cert8_layer_21_5_0 26 cert8_layer_21_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 26 cert8_seen_21_5_1 = cert8_component_21_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_5_1 cert8_layer_21_5_1 25 cert8_layer_21_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 25 cert8_seen_21_5_2 = cert8_component_21_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_5_2 cert8_layer_21_5_2_eq 25

theorem cert8_step_21_5 :
    closedCollarIndexStepBool word fiber8 21 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_21_5)
    (by decide) (by decide)
    (by simpa [cert8_move_21_5] using cert8_component_21_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_21_41 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_21_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_21_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_21_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_21_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.b LColor.p cert8_seen_21_41_0 = cert8_layer_21_41_0 := by
  decide

def cert8_seen_21_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_21_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_21_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.b LColor.p cert8_seen_21_41_1 = cert8_layer_21_41_1 := by
  decide

def cert8_seen_21_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_21_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_21_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.b LColor.p cert8_seen_21_41_2 = cert8_layer_21_41_2 := by
  decide

def cert8_seen_21_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_21_41_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_21_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.b LColor.p cert8_seen_21_41_3 = cert8_layer_21_41_3 := by
  decide

def cert8_seen_21_41_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_21_41_4 : List ChainEdge :=
  []

theorem cert8_layer_21_41_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.b LColor.p cert8_seen_21_41_4 = cert8_layer_21_41_4 := by
  decide

theorem cert8_component_21_41_eq :
    closedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_21_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p 27 cert8_seen_21_41_0 = cert8_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.b LColor.p
    cert8_seen_21_41_0 cert8_layer_21_41_0 26 cert8_layer_21_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p 26 cert8_seen_21_41_1 = cert8_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.b LColor.p
    cert8_seen_21_41_1 cert8_layer_21_41_1 25 cert8_layer_21_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p 25 cert8_seen_21_41_2 = cert8_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.b LColor.p
    cert8_seen_21_41_2 cert8_layer_21_41_2 24 cert8_layer_21_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p 24 cert8_seen_21_41_3 = cert8_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.b LColor.p
    cert8_seen_21_41_3 cert8_layer_21_41_3 23 cert8_layer_21_41_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.b LColor.p 23 cert8_seen_21_41_4 = cert8_component_21_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 21 []) LColor.b LColor.p
    cert8_seen_21_41_4 cert8_layer_21_41_4_eq 23

theorem cert8_step_21_41 :
    closedCollarIndexStepBool word fiber8 21 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_21_41)
    (by decide) (by decide)
    (by simpa [cert8_move_21_41] using cert8_component_21_41_eq)
    (by decide) (by decide) (by decide)

def cert8_move_22_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_22_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_22_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_22_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_22_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_6_0 = cert8_layer_22_6_0 := by
  decide

def cert8_seen_22_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_22_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_22_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_6_1 = cert8_layer_22_6_1 := by
  decide

def cert8_seen_22_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_22_6_2 : List ChainEdge :=
  []

theorem cert8_layer_22_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_6_2 = cert8_layer_22_6_2 := by
  decide

theorem cert8_component_22_6_eq :
    closedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_22_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 27 cert8_seen_22_6_0 = cert8_component_22_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_6_0 cert8_layer_22_6_0 26 cert8_layer_22_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 26 cert8_seen_22_6_1 = cert8_component_22_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_6_1 cert8_layer_22_6_1 25 cert8_layer_22_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 25 cert8_seen_22_6_2 = cert8_component_22_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_6_2 cert8_layer_22_6_2_eq 25

theorem cert8_step_22_6 :
    closedCollarIndexStepBool word fiber8 22 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_22_6)
    (by decide) (by decide)
    (by simpa [cert8_move_22_6] using cert8_component_22_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_22_42 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_22_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_22_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_22_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_22_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.b LColor.p cert8_seen_22_42_0 = cert8_layer_22_42_0 := by
  decide

def cert8_seen_22_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_22_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_22_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.b LColor.p cert8_seen_22_42_1 = cert8_layer_22_42_1 := by
  decide

def cert8_seen_22_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_22_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_22_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.b LColor.p cert8_seen_22_42_2 = cert8_layer_22_42_2 := by
  decide

def cert8_seen_22_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_22_42_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_22_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.b LColor.p cert8_seen_22_42_3 = cert8_layer_22_42_3 := by
  decide

def cert8_seen_22_42_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_22_42_4 : List ChainEdge :=
  []

theorem cert8_layer_22_42_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.b LColor.p cert8_seen_22_42_4 = cert8_layer_22_42_4 := by
  decide

theorem cert8_component_22_42_eq :
    closedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_22_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 22 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p 27 cert8_seen_22_42_0 = cert8_component_22_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.b LColor.p
    cert8_seen_22_42_0 cert8_layer_22_42_0 26 cert8_layer_22_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p 26 cert8_seen_22_42_1 = cert8_component_22_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.b LColor.p
    cert8_seen_22_42_1 cert8_layer_22_42_1 25 cert8_layer_22_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p 25 cert8_seen_22_42_2 = cert8_component_22_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.b LColor.p
    cert8_seen_22_42_2 cert8_layer_22_42_2 24 cert8_layer_22_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p 24 cert8_seen_22_42_3 = cert8_component_22_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.b LColor.p
    cert8_seen_22_42_3 cert8_layer_22_42_3 23 cert8_layer_22_42_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.b LColor.p 23 cert8_seen_22_42_4 = cert8_component_22_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 22 []) LColor.b LColor.p
    cert8_seen_22_42_4 cert8_layer_22_42_4_eq 23

theorem cert8_step_22_42 :
    closedCollarIndexStepBool word fiber8 22 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_22_42)
    (by decide) (by decide)
    (by simpa [cert8_move_22_42] using cert8_component_22_42_eq)
    (by decide) (by decide) (by decide)

def cert8_move_23_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_23_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_23_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_23_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_23_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_7_0 = cert8_layer_23_7_0 := by
  decide

def cert8_seen_23_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_23_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_23_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_7_1 = cert8_layer_23_7_1 := by
  decide

def cert8_seen_23_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_23_7_2 : List ChainEdge :=
  []

theorem cert8_layer_23_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_7_2 = cert8_layer_23_7_2 := by
  decide

theorem cert8_component_23_7_eq :
    closedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_23_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 27 cert8_seen_23_7_0 = cert8_component_23_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_7_0 cert8_layer_23_7_0 26 cert8_layer_23_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 26 cert8_seen_23_7_1 = cert8_component_23_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_7_1 cert8_layer_23_7_1 25 cert8_layer_23_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 25 cert8_seen_23_7_2 = cert8_component_23_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_7_2 cert8_layer_23_7_2_eq 25

theorem cert8_step_23_7 :
    closedCollarIndexStepBool word fiber8 23 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_23_7)
    (by decide) (by decide)
    (by simpa [cert8_move_23_7] using cert8_component_23_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_23_43 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_23_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_23_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_23_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_23_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.b LColor.p cert8_seen_23_43_0 = cert8_layer_23_43_0 := by
  decide

def cert8_seen_23_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_23_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_23_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.b LColor.p cert8_seen_23_43_1 = cert8_layer_23_43_1 := by
  decide

def cert8_seen_23_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_23_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_23_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.b LColor.p cert8_seen_23_43_2 = cert8_layer_23_43_2 := by
  decide

def cert8_seen_23_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_23_43_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_23_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.b LColor.p cert8_seen_23_43_3 = cert8_layer_23_43_3 := by
  decide

def cert8_seen_23_43_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_23_43_4 : List ChainEdge :=
  []

theorem cert8_layer_23_43_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.b LColor.p cert8_seen_23_43_4 = cert8_layer_23_43_4 := by
  decide

theorem cert8_component_23_43_eq :
    closedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_23_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p 27 cert8_seen_23_43_0 = cert8_component_23_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.b LColor.p
    cert8_seen_23_43_0 cert8_layer_23_43_0 26 cert8_layer_23_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p 26 cert8_seen_23_43_1 = cert8_component_23_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.b LColor.p
    cert8_seen_23_43_1 cert8_layer_23_43_1 25 cert8_layer_23_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p 25 cert8_seen_23_43_2 = cert8_component_23_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.b LColor.p
    cert8_seen_23_43_2 cert8_layer_23_43_2 24 cert8_layer_23_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p 24 cert8_seen_23_43_3 = cert8_component_23_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.b LColor.p
    cert8_seen_23_43_3 cert8_layer_23_43_3 23 cert8_layer_23_43_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.b LColor.p 23 cert8_seen_23_43_4 = cert8_component_23_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 23 []) LColor.b LColor.p
    cert8_seen_23_43_4 cert8_layer_23_43_4_eq 23

theorem cert8_step_23_43 :
    closedCollarIndexStepBool word fiber8 23 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_23_43)
    (by decide) (by decide)
    (by simpa [cert8_move_23_43] using cert8_component_23_43_eq)
    (by decide) (by decide) (by decide)

def cert8_move_24_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_24_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_24_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_24_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_24_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_8_0 = cert8_layer_24_8_0 := by
  decide

def cert8_seen_24_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_24_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_24_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_8_1 = cert8_layer_24_8_1 := by
  decide

def cert8_seen_24_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_24_8_2 : List ChainEdge :=
  []

theorem cert8_layer_24_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_8_2 = cert8_layer_24_8_2 := by
  decide

theorem cert8_component_24_8_eq :
    closedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_24_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 27 cert8_seen_24_8_0 = cert8_component_24_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_8_0 cert8_layer_24_8_0 26 cert8_layer_24_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 26 cert8_seen_24_8_1 = cert8_component_24_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_8_1 cert8_layer_24_8_1 25 cert8_layer_24_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 25 cert8_seen_24_8_2 = cert8_component_24_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_8_2 cert8_layer_24_8_2_eq 25

theorem cert8_step_24_8 :
    closedCollarIndexStepBool word fiber8 24 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_24_8)
    (by decide) (by decide)
    (by simpa [cert8_move_24_8] using cert8_component_24_8_eq)
    (by decide) (by decide) (by decide)

def cert8_move_25_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_25_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_25_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_25_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_25_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_9_0 = cert8_layer_25_9_0 := by
  decide

def cert8_seen_25_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_25_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_25_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_9_1 = cert8_layer_25_9_1 := by
  decide

def cert8_seen_25_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_25_9_2 : List ChainEdge :=
  []

theorem cert8_layer_25_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_9_2 = cert8_layer_25_9_2 := by
  decide

theorem cert8_component_25_9_eq :
    closedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_25_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 27 cert8_seen_25_9_0 = cert8_component_25_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_9_0 cert8_layer_25_9_0 26 cert8_layer_25_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 26 cert8_seen_25_9_1 = cert8_component_25_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_9_1 cert8_layer_25_9_1 25 cert8_layer_25_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 25 cert8_seen_25_9_2 = cert8_component_25_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_9_2 cert8_layer_25_9_2_eq 25

theorem cert8_step_25_9 :
    closedCollarIndexStepBool word fiber8 25 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_25_9)
    (by decide) (by decide)
    (by simpa [cert8_move_25_9] using cert8_component_25_9_eq)
    (by decide) (by decide) (by decide)

def cert8_move_26_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_26_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_26_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_26_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_26_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_10_0 = cert8_layer_26_10_0 := by
  decide

def cert8_seen_26_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_26_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_26_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_10_1 = cert8_layer_26_10_1 := by
  decide

def cert8_seen_26_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_26_10_2 : List ChainEdge :=
  []

theorem cert8_layer_26_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_10_2 = cert8_layer_26_10_2 := by
  decide

theorem cert8_component_26_10_eq :
    closedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_26_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 27 cert8_seen_26_10_0 = cert8_component_26_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_10_0 cert8_layer_26_10_0 26 cert8_layer_26_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 26 cert8_seen_26_10_1 = cert8_component_26_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_10_1 cert8_layer_26_10_1 25 cert8_layer_26_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 25 cert8_seen_26_10_2 = cert8_component_26_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_10_2 cert8_layer_26_10_2_eq 25

theorem cert8_step_26_10 :
    closedCollarIndexStepBool word fiber8 26 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_26_10)
    (by decide) (by decide)
    (by simpa [cert8_move_26_10] using cert8_component_26_10_eq)
    (by decide) (by decide) (by decide)

def cert8_move_27_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_27_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_27_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_27_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_27_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_11_0 = cert8_layer_27_11_0 := by
  decide

def cert8_seen_27_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_27_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_27_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_11_1 = cert8_layer_27_11_1 := by
  decide

def cert8_seen_27_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_27_11_2 : List ChainEdge :=
  []

theorem cert8_layer_27_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_11_2 = cert8_layer_27_11_2 := by
  decide

theorem cert8_component_27_11_eq :
    closedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_27_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 27 cert8_seen_27_11_0 = cert8_component_27_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_11_0 cert8_layer_27_11_0 26 cert8_layer_27_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 26 cert8_seen_27_11_1 = cert8_component_27_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_11_1 cert8_layer_27_11_1 25 cert8_layer_27_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 25 cert8_seen_27_11_2 = cert8_component_27_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_11_2 cert8_layer_27_11_2_eq 25

theorem cert8_step_27_11 :
    closedCollarIndexStepBool word fiber8 27 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_27_11)
    (by decide) (by decide)
    (by simpa [cert8_move_27_11] using cert8_component_27_11_eq)
    (by decide) (by decide) (by decide)

def cert8_move_28_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_28_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_28_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_28_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_28_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_12_0 = cert8_layer_28_12_0 := by
  decide

def cert8_seen_28_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_28_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_28_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_12_1 = cert8_layer_28_12_1 := by
  decide

def cert8_seen_28_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_28_12_2 : List ChainEdge :=
  []

theorem cert8_layer_28_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_12_2 = cert8_layer_28_12_2 := by
  decide

theorem cert8_component_28_12_eq :
    closedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_28_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 27 cert8_seen_28_12_0 = cert8_component_28_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_12_0 cert8_layer_28_12_0 26 cert8_layer_28_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 26 cert8_seen_28_12_1 = cert8_component_28_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_12_1 cert8_layer_28_12_1 25 cert8_layer_28_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 25 cert8_seen_28_12_2 = cert8_component_28_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_12_2 cert8_layer_28_12_2_eq 25

theorem cert8_step_28_12 :
    closedCollarIndexStepBool word fiber8 28 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_28_12)
    (by decide) (by decide)
    (by simpa [cert8_move_28_12] using cert8_component_28_12_eq)
    (by decide) (by decide) (by decide)

def cert8_move_29_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_29_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_29_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_29_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_29_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_13_0 = cert8_layer_29_13_0 := by
  decide

def cert8_seen_29_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_29_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_29_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_13_1 = cert8_layer_29_13_1 := by
  decide

def cert8_seen_29_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_29_13_2 : List ChainEdge :=
  []

theorem cert8_layer_29_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_13_2 = cert8_layer_29_13_2 := by
  decide

theorem cert8_component_29_13_eq :
    closedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_29_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 27 cert8_seen_29_13_0 = cert8_component_29_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_13_0 cert8_layer_29_13_0 26 cert8_layer_29_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 26 cert8_seen_29_13_1 = cert8_component_29_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_13_1 cert8_layer_29_13_1 25 cert8_layer_29_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 25 cert8_seen_29_13_2 = cert8_component_29_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_13_2 cert8_layer_29_13_2_eq 25

theorem cert8_step_29_13 :
    closedCollarIndexStepBool word fiber8 29 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_29_13)
    (by decide) (by decide)
    (by simpa [cert8_move_29_13] using cert8_component_29_13_eq)
    (by decide) (by decide) (by decide)

def cert8_move_30_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_30_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_30_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_30_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_30_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_14_0 = cert8_layer_30_14_0 := by
  decide

def cert8_seen_30_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_30_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_30_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_14_1 = cert8_layer_30_14_1 := by
  decide

def cert8_seen_30_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_30_14_2 : List ChainEdge :=
  []

theorem cert8_layer_30_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_14_2 = cert8_layer_30_14_2 := by
  decide

theorem cert8_component_30_14_eq :
    closedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_30_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 27 cert8_seen_30_14_0 = cert8_component_30_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_14_0 cert8_layer_30_14_0 26 cert8_layer_30_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 26 cert8_seen_30_14_1 = cert8_component_30_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_14_1 cert8_layer_30_14_1 25 cert8_layer_30_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 25 cert8_seen_30_14_2 = cert8_component_30_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_14_2 cert8_layer_30_14_2_eq 25

theorem cert8_step_30_14 :
    closedCollarIndexStepBool word fiber8 30 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_30_14)
    (by decide) (by decide)
    (by simpa [cert8_move_30_14] using cert8_component_30_14_eq)
    (by decide) (by decide) (by decide)

def cert8_move_31_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_31_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_31_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_31_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_31_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_15_0 = cert8_layer_31_15_0 := by
  decide

def cert8_seen_31_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_31_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_31_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_15_1 = cert8_layer_31_15_1 := by
  decide

def cert8_seen_31_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_31_15_2 : List ChainEdge :=
  []

theorem cert8_layer_31_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_15_2 = cert8_layer_31_15_2 := by
  decide

theorem cert8_component_31_15_eq :
    closedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert8_component_31_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 27 cert8_seen_31_15_0 = cert8_component_31_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_15_0 cert8_layer_31_15_0 26 cert8_layer_31_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 26 cert8_seen_31_15_1 = cert8_component_31_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_15_1 cert8_layer_31_15_1 25 cert8_layer_31_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 25 cert8_seen_31_15_2 = cert8_component_31_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_15_2 cert8_layer_31_15_2_eq 25

theorem cert8_step_31_15 :
    closedCollarIndexStepBool word fiber8 31 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_31_15)
    (by decide) (by decide)
    (by simpa [cert8_move_31_15] using cert8_component_31_15_eq)
    (by decide) (by decide) (by decide)

def cert8_move_32_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_32_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_32_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_32_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_32_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.b LColor.p cert8_seen_32_4_0 = cert8_layer_32_4_0 := by
  decide

def cert8_seen_32_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_32_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_32_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.b LColor.p cert8_seen_32_4_1 = cert8_layer_32_4_1 := by
  decide

def cert8_seen_32_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_32_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_32_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.b LColor.p cert8_seen_32_4_2 = cert8_layer_32_4_2 := by
  decide

def cert8_seen_32_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_32_4_3 : List ChainEdge :=
  []

theorem cert8_layer_32_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.b LColor.p cert8_seen_32_4_3 = cert8_layer_32_4_3 := by
  decide

theorem cert8_component_32_4_eq :
    closedCollarComponent word (listGetD fiber8 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_32_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.b LColor.p 27 cert8_seen_32_4_0 = cert8_component_32_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.b LColor.p
    cert8_seen_32_4_0 cert8_layer_32_4_0 26 cert8_layer_32_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.b LColor.p 26 cert8_seen_32_4_1 = cert8_component_32_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.b LColor.p
    cert8_seen_32_4_1 cert8_layer_32_4_1 25 cert8_layer_32_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.b LColor.p 25 cert8_seen_32_4_2 = cert8_component_32_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.b LColor.p
    cert8_seen_32_4_2 cert8_layer_32_4_2 24 cert8_layer_32_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.b LColor.p 24 cert8_seen_32_4_3 = cert8_component_32_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 32 []) LColor.b LColor.p
    cert8_seen_32_4_3 cert8_layer_32_4_3_eq 24

theorem cert8_step_32_4 :
    closedCollarIndexStepBool word fiber8 32 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_32_4)
    (by decide) (by decide)
    (by simpa [cert8_move_32_4] using cert8_component_32_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_32_44 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_32_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_32_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_32_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_32_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.p cert8_seen_32_44_0 = cert8_layer_32_44_0 := by
  decide

def cert8_seen_32_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_32_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_32_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.p cert8_seen_32_44_1 = cert8_layer_32_44_1 := by
  decide

def cert8_seen_32_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_32_44_2 : List ChainEdge :=
  []

theorem cert8_layer_32_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.p cert8_seen_32_44_2 = cert8_layer_32_44_2 := by
  decide

theorem cert8_component_32_44_eq :
    closedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_32_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.p 27 cert8_seen_32_44_0 = cert8_component_32_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.p
    cert8_seen_32_44_0 cert8_layer_32_44_0 26 cert8_layer_32_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.p 26 cert8_seen_32_44_1 = cert8_component_32_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.p
    cert8_seen_32_44_1 cert8_layer_32_44_1 25 cert8_layer_32_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.p 25 cert8_seen_32_44_2 = cert8_component_32_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 32 []) LColor.r LColor.p
    cert8_seen_32_44_2 cert8_layer_32_44_2_eq 25

theorem cert8_step_32_44 :
    closedCollarIndexStepBool word fiber8 32 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_32_44)
    (by decide) (by decide)
    (by simpa [cert8_move_32_44] using cert8_component_32_44_eq)
    (by decide) (by decide) (by decide)

def cert8_move_33_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_33_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_33_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_33_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_33_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.b LColor.p cert8_seen_33_5_0 = cert8_layer_33_5_0 := by
  decide

def cert8_seen_33_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_33_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_33_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.b LColor.p cert8_seen_33_5_1 = cert8_layer_33_5_1 := by
  decide

def cert8_seen_33_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_33_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_33_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.b LColor.p cert8_seen_33_5_2 = cert8_layer_33_5_2 := by
  decide

def cert8_seen_33_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_33_5_3 : List ChainEdge :=
  []

theorem cert8_layer_33_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.b LColor.p cert8_seen_33_5_3 = cert8_layer_33_5_3 := by
  decide

theorem cert8_component_33_5_eq :
    closedCollarComponent word (listGetD fiber8 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_33_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.b LColor.p 27 cert8_seen_33_5_0 = cert8_component_33_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.b LColor.p
    cert8_seen_33_5_0 cert8_layer_33_5_0 26 cert8_layer_33_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.b LColor.p 26 cert8_seen_33_5_1 = cert8_component_33_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.b LColor.p
    cert8_seen_33_5_1 cert8_layer_33_5_1 25 cert8_layer_33_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.b LColor.p 25 cert8_seen_33_5_2 = cert8_component_33_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.b LColor.p
    cert8_seen_33_5_2 cert8_layer_33_5_2 24 cert8_layer_33_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.b LColor.p 24 cert8_seen_33_5_3 = cert8_component_33_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 33 []) LColor.b LColor.p
    cert8_seen_33_5_3 cert8_layer_33_5_3_eq 24

theorem cert8_step_33_5 :
    closedCollarIndexStepBool word fiber8 33 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_33_5)
    (by decide) (by decide)
    (by simpa [cert8_move_33_5] using cert8_component_33_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_33_45 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_33_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_33_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_33_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_33_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.p cert8_seen_33_45_0 = cert8_layer_33_45_0 := by
  decide

def cert8_seen_33_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_33_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_33_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.p cert8_seen_33_45_1 = cert8_layer_33_45_1 := by
  decide

def cert8_seen_33_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_33_45_2 : List ChainEdge :=
  []

theorem cert8_layer_33_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.p cert8_seen_33_45_2 = cert8_layer_33_45_2 := by
  decide

theorem cert8_component_33_45_eq :
    closedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_33_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.p 27 cert8_seen_33_45_0 = cert8_component_33_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.p
    cert8_seen_33_45_0 cert8_layer_33_45_0 26 cert8_layer_33_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.p 26 cert8_seen_33_45_1 = cert8_component_33_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.p
    cert8_seen_33_45_1 cert8_layer_33_45_1 25 cert8_layer_33_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.p 25 cert8_seen_33_45_2 = cert8_component_33_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 33 []) LColor.r LColor.p
    cert8_seen_33_45_2 cert8_layer_33_45_2_eq 25

theorem cert8_step_33_45 :
    closedCollarIndexStepBool word fiber8 33 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_33_45)
    (by decide) (by decide)
    (by simpa [cert8_move_33_45] using cert8_component_33_45_eq)
    (by decide) (by decide) (by decide)

def cert8_move_34_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_34_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_34_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_34_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_34_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.b LColor.p cert8_seen_34_6_0 = cert8_layer_34_6_0 := by
  decide

def cert8_seen_34_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_34_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_34_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.b LColor.p cert8_seen_34_6_1 = cert8_layer_34_6_1 := by
  decide

def cert8_seen_34_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_34_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_34_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.b LColor.p cert8_seen_34_6_2 = cert8_layer_34_6_2 := by
  decide

def cert8_seen_34_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_34_6_3 : List ChainEdge :=
  []

theorem cert8_layer_34_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.b LColor.p cert8_seen_34_6_3 = cert8_layer_34_6_3 := by
  decide

theorem cert8_component_34_6_eq :
    closedCollarComponent word (listGetD fiber8 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_34_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.b LColor.p 27 cert8_seen_34_6_0 = cert8_component_34_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.b LColor.p
    cert8_seen_34_6_0 cert8_layer_34_6_0 26 cert8_layer_34_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.b LColor.p 26 cert8_seen_34_6_1 = cert8_component_34_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.b LColor.p
    cert8_seen_34_6_1 cert8_layer_34_6_1 25 cert8_layer_34_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.b LColor.p 25 cert8_seen_34_6_2 = cert8_component_34_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.b LColor.p
    cert8_seen_34_6_2 cert8_layer_34_6_2 24 cert8_layer_34_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.b LColor.p 24 cert8_seen_34_6_3 = cert8_component_34_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 34 []) LColor.b LColor.p
    cert8_seen_34_6_3 cert8_layer_34_6_3_eq 24

theorem cert8_step_34_6 :
    closedCollarIndexStepBool word fiber8 34 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_34_6)
    (by decide) (by decide)
    (by simpa [cert8_move_34_6] using cert8_component_34_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_34_46 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_34_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_34_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_34_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_34_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.p cert8_seen_34_46_0 = cert8_layer_34_46_0 := by
  decide

def cert8_seen_34_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_34_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_34_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.p cert8_seen_34_46_1 = cert8_layer_34_46_1 := by
  decide

def cert8_seen_34_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_34_46_2 : List ChainEdge :=
  []

theorem cert8_layer_34_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.p cert8_seen_34_46_2 = cert8_layer_34_46_2 := by
  decide

theorem cert8_component_34_46_eq :
    closedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_34_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.p 27 cert8_seen_34_46_0 = cert8_component_34_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.p
    cert8_seen_34_46_0 cert8_layer_34_46_0 26 cert8_layer_34_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.p 26 cert8_seen_34_46_1 = cert8_component_34_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.p
    cert8_seen_34_46_1 cert8_layer_34_46_1 25 cert8_layer_34_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.p 25 cert8_seen_34_46_2 = cert8_component_34_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 34 []) LColor.r LColor.p
    cert8_seen_34_46_2 cert8_layer_34_46_2_eq 25

theorem cert8_step_34_46 :
    closedCollarIndexStepBool word fiber8 34 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_34_46)
    (by decide) (by decide)
    (by simpa [cert8_move_34_46] using cert8_component_34_46_eq)
    (by decide) (by decide) (by decide)

def cert8_move_35_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_35_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_35_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_35_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_35_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.b LColor.p cert8_seen_35_7_0 = cert8_layer_35_7_0 := by
  decide

def cert8_seen_35_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_35_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_35_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.b LColor.p cert8_seen_35_7_1 = cert8_layer_35_7_1 := by
  decide

def cert8_seen_35_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_35_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_35_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.b LColor.p cert8_seen_35_7_2 = cert8_layer_35_7_2 := by
  decide

def cert8_seen_35_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_35_7_3 : List ChainEdge :=
  []

theorem cert8_layer_35_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.b LColor.p cert8_seen_35_7_3 = cert8_layer_35_7_3 := by
  decide

theorem cert8_component_35_7_eq :
    closedCollarComponent word (listGetD fiber8 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_35_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.b LColor.p 27 cert8_seen_35_7_0 = cert8_component_35_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.b LColor.p
    cert8_seen_35_7_0 cert8_layer_35_7_0 26 cert8_layer_35_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.b LColor.p 26 cert8_seen_35_7_1 = cert8_component_35_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.b LColor.p
    cert8_seen_35_7_1 cert8_layer_35_7_1 25 cert8_layer_35_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.b LColor.p 25 cert8_seen_35_7_2 = cert8_component_35_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.b LColor.p
    cert8_seen_35_7_2 cert8_layer_35_7_2 24 cert8_layer_35_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.b LColor.p 24 cert8_seen_35_7_3 = cert8_component_35_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 35 []) LColor.b LColor.p
    cert8_seen_35_7_3 cert8_layer_35_7_3_eq 24

theorem cert8_step_35_7 :
    closedCollarIndexStepBool word fiber8 35 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_35_7)
    (by decide) (by decide)
    (by simpa [cert8_move_35_7] using cert8_component_35_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_35_47 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_35_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_35_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_35_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_35_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.p cert8_seen_35_47_0 = cert8_layer_35_47_0 := by
  decide

def cert8_seen_35_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_35_47_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_35_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.p cert8_seen_35_47_1 = cert8_layer_35_47_1 := by
  decide

def cert8_seen_35_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_35_47_2 : List ChainEdge :=
  []

theorem cert8_layer_35_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.p cert8_seen_35_47_2 = cert8_layer_35_47_2 := by
  decide

theorem cert8_component_35_47_eq :
    closedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_35_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.p 27 cert8_seen_35_47_0 = cert8_component_35_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.p
    cert8_seen_35_47_0 cert8_layer_35_47_0 26 cert8_layer_35_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.p 26 cert8_seen_35_47_1 = cert8_component_35_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.p
    cert8_seen_35_47_1 cert8_layer_35_47_1 25 cert8_layer_35_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.p 25 cert8_seen_35_47_2 = cert8_component_35_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 35 []) LColor.r LColor.p
    cert8_seen_35_47_2 cert8_layer_35_47_2_eq 25

theorem cert8_step_35_47 :
    closedCollarIndexStepBool word fiber8 35 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_35_47)
    (by decide) (by decide)
    (by simpa [cert8_move_35_47] using cert8_component_35_47_eq)
    (by decide) (by decide) (by decide)

def cert8_move_36_12 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_36_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_36_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_12_0 = cert8_layer_36_12_0 := by
  decide

def cert8_seen_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_36_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_12_1 = cert8_layer_36_12_1 := by
  decide

def cert8_seen_36_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_36_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_36_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_12_2 = cert8_layer_36_12_2 := by
  decide

def cert8_seen_36_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_36_12_3 : List ChainEdge :=
  []

theorem cert8_layer_36_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_12_3 = cert8_layer_36_12_3 := by
  decide

theorem cert8_component_36_12_eq :
    closedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_36_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 27 cert8_seen_36_12_0 = cert8_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_12_0 cert8_layer_36_12_0 26 cert8_layer_36_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 26 cert8_seen_36_12_1 = cert8_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_12_1 cert8_layer_36_12_1 25 cert8_layer_36_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 25 cert8_seen_36_12_2 = cert8_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_12_2 cert8_layer_36_12_2 24 cert8_layer_36_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 24 cert8_seen_36_12_3 = cert8_component_36_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_12_3 cert8_layer_36_12_3_eq 24

theorem cert8_step_36_12 :
    closedCollarIndexStepBool word fiber8 36 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_36_12)
    (by decide) (by decide)
    (by simpa [cert8_move_36_12] using cert8_component_36_12_eq)
    (by decide) (by decide) (by decide)

def cert8_move_37_13 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_37_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_37_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_13_0 = cert8_layer_37_13_0 := by
  decide

def cert8_seen_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_37_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_13_1 = cert8_layer_37_13_1 := by
  decide

def cert8_seen_37_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_37_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_37_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_13_2 = cert8_layer_37_13_2 := by
  decide

def cert8_seen_37_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_37_13_3 : List ChainEdge :=
  []

theorem cert8_layer_37_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_13_3 = cert8_layer_37_13_3 := by
  decide

theorem cert8_component_37_13_eq :
    closedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_37_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 27 cert8_seen_37_13_0 = cert8_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_13_0 cert8_layer_37_13_0 26 cert8_layer_37_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 26 cert8_seen_37_13_1 = cert8_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_13_1 cert8_layer_37_13_1 25 cert8_layer_37_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 25 cert8_seen_37_13_2 = cert8_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_13_2 cert8_layer_37_13_2 24 cert8_layer_37_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 24 cert8_seen_37_13_3 = cert8_component_37_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_13_3 cert8_layer_37_13_3_eq 24

theorem cert8_step_37_13 :
    closedCollarIndexStepBool word fiber8 37 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_37_13)
    (by decide) (by decide)
    (by simpa [cert8_move_37_13] using cert8_component_37_13_eq)
    (by decide) (by decide) (by decide)

def cert8_move_38_14 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_38_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_38_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_14_0 = cert8_layer_38_14_0 := by
  decide

def cert8_seen_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_38_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_14_1 = cert8_layer_38_14_1 := by
  decide

def cert8_seen_38_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_38_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_38_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_14_2 = cert8_layer_38_14_2 := by
  decide

def cert8_seen_38_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_38_14_3 : List ChainEdge :=
  []

theorem cert8_layer_38_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_14_3 = cert8_layer_38_14_3 := by
  decide

theorem cert8_component_38_14_eq :
    closedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_38_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 27 cert8_seen_38_14_0 = cert8_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_14_0 cert8_layer_38_14_0 26 cert8_layer_38_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 26 cert8_seen_38_14_1 = cert8_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_14_1 cert8_layer_38_14_1 25 cert8_layer_38_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 25 cert8_seen_38_14_2 = cert8_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_14_2 cert8_layer_38_14_2 24 cert8_layer_38_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 24 cert8_seen_38_14_3 = cert8_component_38_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_14_3 cert8_layer_38_14_3_eq 24

theorem cert8_step_38_14 :
    closedCollarIndexStepBool word fiber8 38 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_38_14)
    (by decide) (by decide)
    (by simpa [cert8_move_38_14] using cert8_component_38_14_eq)
    (by decide) (by decide) (by decide)

def cert8_move_39_15 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_39_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_39_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_15_0 = cert8_layer_39_15_0 := by
  decide

def cert8_seen_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_39_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_15_1 = cert8_layer_39_15_1 := by
  decide

def cert8_seen_39_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_39_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_39_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_15_2 = cert8_layer_39_15_2 := by
  decide

def cert8_seen_39_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_39_15_3 : List ChainEdge :=
  []

theorem cert8_layer_39_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_15_3 = cert8_layer_39_15_3 := by
  decide

theorem cert8_component_39_15_eq :
    closedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_39_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 27 cert8_seen_39_15_0 = cert8_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_15_0 cert8_layer_39_15_0 26 cert8_layer_39_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 26 cert8_seen_39_15_1 = cert8_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_15_1 cert8_layer_39_15_1 25 cert8_layer_39_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 25 cert8_seen_39_15_2 = cert8_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_15_2 cert8_layer_39_15_2 24 cert8_layer_39_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 24 cert8_seen_39_15_3 = cert8_component_39_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_15_3 cert8_layer_39_15_3_eq 24

theorem cert8_step_39_15 :
    closedCollarIndexStepBool word fiber8 39 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_39_15)
    (by decide) (by decide)
    (by simpa [cert8_move_39_15] using cert8_component_39_15_eq)
    (by decide) (by decide) (by decide)

def cert8_move_40_20 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_40_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_40_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_40_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_40_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_20_0 = cert8_layer_40_20_0 := by
  decide

def cert8_seen_40_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_40_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_40_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_20_1 = cert8_layer_40_20_1 := by
  decide

def cert8_seen_40_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_40_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_40_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_20_2 = cert8_layer_40_20_2 := by
  decide

def cert8_seen_40_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_40_20_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_40_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_20_3 = cert8_layer_40_20_3 := by
  decide

def cert8_seen_40_20_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_40_20_4 : List ChainEdge :=
  []

theorem cert8_layer_40_20_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_20_4 = cert8_layer_40_20_4 := by
  decide

theorem cert8_component_40_20_eq :
    closedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_40_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 27 cert8_seen_40_20_0 = cert8_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_20_0 cert8_layer_40_20_0 26 cert8_layer_40_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 26 cert8_seen_40_20_1 = cert8_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_20_1 cert8_layer_40_20_1 25 cert8_layer_40_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 25 cert8_seen_40_20_2 = cert8_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_20_2 cert8_layer_40_20_2 24 cert8_layer_40_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 24 cert8_seen_40_20_3 = cert8_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_20_3 cert8_layer_40_20_3 23 cert8_layer_40_20_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 23 cert8_seen_40_20_4 = cert8_component_40_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_20_4 cert8_layer_40_20_4_eq 23

theorem cert8_step_40_20 :
    closedCollarIndexStepBool word fiber8 40 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_40_20)
    (by decide) (by decide)
    (by simpa [cert8_move_40_20] using cert8_component_40_20_eq)
    (by decide) (by decide) (by decide)

def cert8_move_41_21 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_41_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_41_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_41_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_41_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_21_0 = cert8_layer_41_21_0 := by
  decide

def cert8_seen_41_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_41_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_41_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_21_1 = cert8_layer_41_21_1 := by
  decide

def cert8_seen_41_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_41_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_41_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_21_2 = cert8_layer_41_21_2 := by
  decide

def cert8_seen_41_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_41_21_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_41_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_21_3 = cert8_layer_41_21_3 := by
  decide

def cert8_seen_41_21_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_41_21_4 : List ChainEdge :=
  []

theorem cert8_layer_41_21_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_21_4 = cert8_layer_41_21_4 := by
  decide

theorem cert8_component_41_21_eq :
    closedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_41_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 27 cert8_seen_41_21_0 = cert8_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_21_0 cert8_layer_41_21_0 26 cert8_layer_41_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 26 cert8_seen_41_21_1 = cert8_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_21_1 cert8_layer_41_21_1 25 cert8_layer_41_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 25 cert8_seen_41_21_2 = cert8_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_21_2 cert8_layer_41_21_2 24 cert8_layer_41_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 24 cert8_seen_41_21_3 = cert8_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_21_3 cert8_layer_41_21_3 23 cert8_layer_41_21_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 23 cert8_seen_41_21_4 = cert8_component_41_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_21_4 cert8_layer_41_21_4_eq 23

theorem cert8_step_41_21 :
    closedCollarIndexStepBool word fiber8 41 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_41_21)
    (by decide) (by decide)
    (by simpa [cert8_move_41_21] using cert8_component_41_21_eq)
    (by decide) (by decide) (by decide)

def cert8_move_42_22 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_42_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_42_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_42_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_42_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.b LColor.p cert8_seen_42_22_0 = cert8_layer_42_22_0 := by
  decide

def cert8_seen_42_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_42_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_42_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.b LColor.p cert8_seen_42_22_1 = cert8_layer_42_22_1 := by
  decide

def cert8_seen_42_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_42_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_42_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.b LColor.p cert8_seen_42_22_2 = cert8_layer_42_22_2 := by
  decide

def cert8_seen_42_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_42_22_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_42_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.b LColor.p cert8_seen_42_22_3 = cert8_layer_42_22_3 := by
  decide

def cert8_seen_42_22_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_42_22_4 : List ChainEdge :=
  []

theorem cert8_layer_42_22_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.b LColor.p cert8_seen_42_22_4 = cert8_layer_42_22_4 := by
  decide

theorem cert8_component_42_22_eq :
    closedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_42_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p 27 cert8_seen_42_22_0 = cert8_component_42_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.b LColor.p
    cert8_seen_42_22_0 cert8_layer_42_22_0 26 cert8_layer_42_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p 26 cert8_seen_42_22_1 = cert8_component_42_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.b LColor.p
    cert8_seen_42_22_1 cert8_layer_42_22_1 25 cert8_layer_42_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p 25 cert8_seen_42_22_2 = cert8_component_42_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.b LColor.p
    cert8_seen_42_22_2 cert8_layer_42_22_2 24 cert8_layer_42_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p 24 cert8_seen_42_22_3 = cert8_component_42_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.b LColor.p
    cert8_seen_42_22_3 cert8_layer_42_22_3 23 cert8_layer_42_22_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.b LColor.p 23 cert8_seen_42_22_4 = cert8_component_42_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 42 []) LColor.b LColor.p
    cert8_seen_42_22_4 cert8_layer_42_22_4_eq 23

theorem cert8_step_42_22 :
    closedCollarIndexStepBool word fiber8 42 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_42_22)
    (by decide) (by decide)
    (by simpa [cert8_move_42_22] using cert8_component_42_22_eq)
    (by decide) (by decide) (by decide)

def cert8_move_43_23 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_43_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_43_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_43_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_43_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.b LColor.p cert8_seen_43_23_0 = cert8_layer_43_23_0 := by
  decide

def cert8_seen_43_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_43_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_43_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.b LColor.p cert8_seen_43_23_1 = cert8_layer_43_23_1 := by
  decide

def cert8_seen_43_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_43_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_43_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.b LColor.p cert8_seen_43_23_2 = cert8_layer_43_23_2 := by
  decide

def cert8_seen_43_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_43_23_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_43_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.b LColor.p cert8_seen_43_23_3 = cert8_layer_43_23_3 := by
  decide

def cert8_seen_43_23_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_43_23_4 : List ChainEdge :=
  []

theorem cert8_layer_43_23_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.b LColor.p cert8_seen_43_23_4 = cert8_layer_43_23_4 := by
  decide

theorem cert8_component_43_23_eq :
    closedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert8_component_43_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p 27 cert8_seen_43_23_0 = cert8_component_43_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.b LColor.p
    cert8_seen_43_23_0 cert8_layer_43_23_0 26 cert8_layer_43_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p 26 cert8_seen_43_23_1 = cert8_component_43_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.b LColor.p
    cert8_seen_43_23_1 cert8_layer_43_23_1 25 cert8_layer_43_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p 25 cert8_seen_43_23_2 = cert8_component_43_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.b LColor.p
    cert8_seen_43_23_2 cert8_layer_43_23_2 24 cert8_layer_43_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p 24 cert8_seen_43_23_3 = cert8_component_43_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.b LColor.p
    cert8_seen_43_23_3 cert8_layer_43_23_3 23 cert8_layer_43_23_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.b LColor.p 23 cert8_seen_43_23_4 = cert8_component_43_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 43 []) LColor.b LColor.p
    cert8_seen_43_23_4 cert8_layer_43_23_4_eq 23

theorem cert8_step_43_23 :
    closedCollarIndexStepBool word fiber8 43 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_43_23)
    (by decide) (by decide)
    (by simpa [cert8_move_43_23] using cert8_component_43_23_eq)
    (by decide) (by decide) (by decide)

def cert8_move_44_32 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_44_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_44_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_44_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_44_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.p cert8_seen_44_32_0 = cert8_layer_44_32_0 := by
  decide

def cert8_seen_44_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_44_32_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_44_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.p cert8_seen_44_32_1 = cert8_layer_44_32_1 := by
  decide

def cert8_seen_44_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_44_32_2 : List ChainEdge :=
  []

theorem cert8_layer_44_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.p cert8_seen_44_32_2 = cert8_layer_44_32_2 := by
  decide

theorem cert8_component_44_32_eq :
    closedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_44_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.p 27 cert8_seen_44_32_0 = cert8_component_44_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 44 []) LColor.r LColor.p
    cert8_seen_44_32_0 cert8_layer_44_32_0 26 cert8_layer_44_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.p 26 cert8_seen_44_32_1 = cert8_component_44_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 44 []) LColor.r LColor.p
    cert8_seen_44_32_1 cert8_layer_44_32_1 25 cert8_layer_44_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.p 25 cert8_seen_44_32_2 = cert8_component_44_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 44 []) LColor.r LColor.p
    cert8_seen_44_32_2 cert8_layer_44_32_2_eq 25

theorem cert8_step_44_32 :
    closedCollarIndexStepBool word fiber8 44 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_44_32)
    (by decide) (by decide)
    (by simpa [cert8_move_44_32] using cert8_component_44_32_eq)
    (by decide) (by decide) (by decide)

def cert8_move_45_33 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_45_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_45_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_45_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_45_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.p cert8_seen_45_33_0 = cert8_layer_45_33_0 := by
  decide

def cert8_seen_45_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_45_33_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_45_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.p cert8_seen_45_33_1 = cert8_layer_45_33_1 := by
  decide

def cert8_seen_45_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_45_33_2 : List ChainEdge :=
  []

theorem cert8_layer_45_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.p cert8_seen_45_33_2 = cert8_layer_45_33_2 := by
  decide

theorem cert8_component_45_33_eq :
    closedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_45_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.p 27 cert8_seen_45_33_0 = cert8_component_45_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 45 []) LColor.r LColor.p
    cert8_seen_45_33_0 cert8_layer_45_33_0 26 cert8_layer_45_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.p 26 cert8_seen_45_33_1 = cert8_component_45_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 45 []) LColor.r LColor.p
    cert8_seen_45_33_1 cert8_layer_45_33_1 25 cert8_layer_45_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.p 25 cert8_seen_45_33_2 = cert8_component_45_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 45 []) LColor.r LColor.p
    cert8_seen_45_33_2 cert8_layer_45_33_2_eq 25

theorem cert8_step_45_33 :
    closedCollarIndexStepBool word fiber8 45 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_45_33)
    (by decide) (by decide)
    (by simpa [cert8_move_45_33] using cert8_component_45_33_eq)
    (by decide) (by decide) (by decide)

def cert8_move_46_34 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_46_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_46_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_46_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_46_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.p cert8_seen_46_34_0 = cert8_layer_46_34_0 := by
  decide

def cert8_seen_46_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_46_34_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_46_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.p cert8_seen_46_34_1 = cert8_layer_46_34_1 := by
  decide

def cert8_seen_46_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_46_34_2 : List ChainEdge :=
  []

theorem cert8_layer_46_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.p cert8_seen_46_34_2 = cert8_layer_46_34_2 := by
  decide

theorem cert8_component_46_34_eq :
    closedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_46_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.p 27 cert8_seen_46_34_0 = cert8_component_46_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.p
    cert8_seen_46_34_0 cert8_layer_46_34_0 26 cert8_layer_46_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.p 26 cert8_seen_46_34_1 = cert8_component_46_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.p
    cert8_seen_46_34_1 cert8_layer_46_34_1 25 cert8_layer_46_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.p 25 cert8_seen_46_34_2 = cert8_component_46_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 46 []) LColor.r LColor.p
    cert8_seen_46_34_2 cert8_layer_46_34_2_eq 25

theorem cert8_step_46_34 :
    closedCollarIndexStepBool word fiber8 46 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_46_34)
    (by decide) (by decide)
    (by simpa [cert8_move_46_34] using cert8_component_46_34_eq)
    (by decide) (by decide) (by decide)

def cert8_move_47_35 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_47_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_47_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_47_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_47_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.p cert8_seen_47_35_0 = cert8_layer_47_35_0 := by
  decide

def cert8_seen_47_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_47_35_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_47_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.p cert8_seen_47_35_1 = cert8_layer_47_35_1 := by
  decide

def cert8_seen_47_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_47_35_2 : List ChainEdge :=
  []

theorem cert8_layer_47_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.p cert8_seen_47_35_2 = cert8_layer_47_35_2 := by
  decide

theorem cert8_component_47_35_eq :
    closedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_47_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.p 27 cert8_seen_47_35_0 = cert8_component_47_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.p
    cert8_seen_47_35_0 cert8_layer_47_35_0 26 cert8_layer_47_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.p 26 cert8_seen_47_35_1 = cert8_component_47_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.p
    cert8_seen_47_35_1 cert8_layer_47_35_1 25 cert8_layer_47_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.p 25 cert8_seen_47_35_2 = cert8_component_47_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 47 []) LColor.r LColor.p
    cert8_seen_47_35_2 cert8_layer_47_35_2_eq 25

theorem cert8_step_47_35 :
    closedCollarIndexStepBool word fiber8 47 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_47_35)
    (by decide) (by decide)
    (by simpa [cert8_move_47_35] using cert8_component_47_35_eq)
    (by decide) (by decide) (by decide)

theorem cert8_row_0 :
    closedCollarParentIndexValid word fiber8 cert8.parents 0 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length]

theorem cert8_row_1 :
    closedCollarParentIndexValid word fiber8 cert8.parents 1 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_1_0, cert8_step_0_1]

theorem cert8_row_2 :
    closedCollarParentIndexValid word fiber8 cert8.parents 2 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_2_1, cert8_step_1_2]

theorem cert8_row_3 :
    closedCollarParentIndexValid word fiber8 cert8.parents 3 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_3_0, cert8_step_0_3]

theorem cert8_row_4 :
    closedCollarParentIndexValid word fiber8 cert8.parents 4 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_4_0, cert8_step_0_4]

theorem cert8_row_5 :
    closedCollarParentIndexValid word fiber8 cert8.parents 5 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_5_1, cert8_step_1_5]

theorem cert8_row_6 :
    closedCollarParentIndexValid word fiber8 cert8.parents 6 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_6_4, cert8_step_4_6]

theorem cert8_row_7 :
    closedCollarParentIndexValid word fiber8 cert8.parents 7 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_7_3, cert8_step_3_7]

theorem cert8_row_8 :
    closedCollarParentIndexValid word fiber8 cert8.parents 8 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_8_0, cert8_step_0_8]

theorem cert8_row_9 :
    closedCollarParentIndexValid word fiber8 cert8.parents 9 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_9_1, cert8_step_1_9]

theorem cert8_row_10 :
    closedCollarParentIndexValid word fiber8 cert8.parents 10 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_10_2, cert8_step_2_10]

theorem cert8_row_11 :
    closedCollarParentIndexValid word fiber8 cert8.parents 11 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_11_3, cert8_step_3_11]

theorem cert8_row_12 :
    closedCollarParentIndexValid word fiber8 cert8.parents 12 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_12_4, cert8_step_4_12]

theorem cert8_row_13 :
    closedCollarParentIndexValid word fiber8 cert8.parents 13 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_13_5, cert8_step_5_13]

theorem cert8_row_14 :
    closedCollarParentIndexValid word fiber8 cert8.parents 14 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_14_6, cert8_step_6_14]

theorem cert8_row_15 :
    closedCollarParentIndexValid word fiber8 cert8.parents 15 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_15_7, cert8_step_7_15]

theorem cert8_row_16 :
    closedCollarParentIndexValid word fiber8 cert8.parents 16 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_16_0, cert8_step_0_16]

theorem cert8_row_17 :
    closedCollarParentIndexValid word fiber8 cert8.parents 17 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_17_1, cert8_step_1_17]

theorem cert8_row_18 :
    closedCollarParentIndexValid word fiber8 cert8.parents 18 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_18_2, cert8_step_2_18]

theorem cert8_row_19 :
    closedCollarParentIndexValid word fiber8 cert8.parents 19 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_19_3, cert8_step_3_19]

theorem cert8_row_20 :
    closedCollarParentIndexValid word fiber8 cert8.parents 20 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_20_4, cert8_step_4_20]

theorem cert8_row_21 :
    closedCollarParentIndexValid word fiber8 cert8.parents 21 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_21_5, cert8_step_5_21]

theorem cert8_row_22 :
    closedCollarParentIndexValid word fiber8 cert8.parents 22 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_22_6, cert8_step_6_22]

theorem cert8_row_23 :
    closedCollarParentIndexValid word fiber8 cert8.parents 23 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_23_7, cert8_step_7_23]

theorem cert8_row_24 :
    closedCollarParentIndexValid word fiber8 cert8.parents 24 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_24_8, cert8_step_8_24]

theorem cert8_row_25 :
    closedCollarParentIndexValid word fiber8 cert8.parents 25 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_25_9, cert8_step_9_25]

theorem cert8_row_26 :
    closedCollarParentIndexValid word fiber8 cert8.parents 26 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_26_10, cert8_step_10_26]

theorem cert8_row_27 :
    closedCollarParentIndexValid word fiber8 cert8.parents 27 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_27_11, cert8_step_11_27]

theorem cert8_row_28 :
    closedCollarParentIndexValid word fiber8 cert8.parents 28 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_28_12, cert8_step_12_28]

theorem cert8_row_29 :
    closedCollarParentIndexValid word fiber8 cert8.parents 29 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_29_13, cert8_step_13_29]

theorem cert8_row_30 :
    closedCollarParentIndexValid word fiber8 cert8.parents 30 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_30_14, cert8_step_14_30]

theorem cert8_row_31 :
    closedCollarParentIndexValid word fiber8 cert8.parents 31 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_31_15, cert8_step_15_31]

theorem cert8_row_32 :
    closedCollarParentIndexValid word fiber8 cert8.parents 32 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_32_4, cert8_step_4_32]

theorem cert8_row_33 :
    closedCollarParentIndexValid word fiber8 cert8.parents 33 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_33_5, cert8_step_5_33]

theorem cert8_row_34 :
    closedCollarParentIndexValid word fiber8 cert8.parents 34 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_34_6, cert8_step_6_34]

theorem cert8_row_35 :
    closedCollarParentIndexValid word fiber8 cert8.parents 35 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_35_7, cert8_step_7_35]

theorem cert8_row_36 :
    closedCollarParentIndexValid word fiber8 cert8.parents 36 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_36_12, cert8_step_12_36]

theorem cert8_row_37 :
    closedCollarParentIndexValid word fiber8 cert8.parents 37 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_37_13, cert8_step_13_37]

theorem cert8_row_38 :
    closedCollarParentIndexValid word fiber8 cert8.parents 38 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_38_14, cert8_step_14_38]

theorem cert8_row_39 :
    closedCollarParentIndexValid word fiber8 cert8.parents 39 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_39_15, cert8_step_15_39]

theorem cert8_row_40 :
    closedCollarParentIndexValid word fiber8 cert8.parents 40 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_40_20, cert8_step_20_40]

theorem cert8_row_41 :
    closedCollarParentIndexValid word fiber8 cert8.parents 41 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_41_21, cert8_step_21_41]

theorem cert8_row_42 :
    closedCollarParentIndexValid word fiber8 cert8.parents 42 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_42_22, cert8_step_22_42]

theorem cert8_row_43 :
    closedCollarParentIndexValid word fiber8 cert8.parents 43 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_43_23, cert8_step_23_43]

theorem cert8_row_44 :
    closedCollarParentIndexValid word fiber8 cert8.parents 44 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_44_32, cert8_step_32_44]

theorem cert8_row_45 :
    closedCollarParentIndexValid word fiber8 cert8.parents 45 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_45_33, cert8_step_33_45]

theorem cert8_row_46 :
    closedCollarParentIndexValid word fiber8 cert8.parents 46 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_46_34, cert8_step_34_46]

theorem cert8_row_47 :
    closedCollarParentIndexValid word fiber8 cert8.parents 47 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_47_35, cert8_step_35_47]

theorem cert8_rows :
    closedCollarSpineRowsValid word fiber8 cert8.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert8_fiber_length : fiber8.length = 48 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert8_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert8_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert8_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert8_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert8_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert8_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert8_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert8_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert8_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert8_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert8_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert8_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert8_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert8_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert8_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert8_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert8_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert8_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert8_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert8_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert8_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert8_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert8_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert8_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert8_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert8_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert8_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert8_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert8_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert8_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert8_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert8_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert8_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert8_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert8_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert8_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert8_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert8_row_43
  by_cases h44 : idx = 44
  · subst idx
    exact cert8_row_44
  by_cases h45 : idx = 45
  · subst idx
    exact cert8_row_45
  by_cases h46 : idx = 46
  · subst idx
    exact cert8_row_46
  by_cases h47 : idx = 47
  · subst idx
    exact cert8_row_47
  · omega

theorem cert8_root :
    closedCollarSpineParentsReachRoot fiber8 cert8 = true := by
  decide

theorem cert8_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert8.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert8 fiber8_eq cert8_rows cert8_root


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
