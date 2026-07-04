import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

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
, []
, []
, []
, []
, []
, []
, []
, [
  [stateAt 132, stateAt 88, stateAt 83]
, [stateAt 132, stateAt 89, stateAt 91]
, [stateAt 132, stateAt 90, stateAt 19]
, [stateAt 132, stateAt 91, stateAt 27]
, [stateAt 132, stateAt 110, stateAt 67]
, [stateAt 132, stateAt 111, stateAt 75]
, [stateAt 133, stateAt 80, stateAt 83]
, [stateAt 133, stateAt 81, stateAt 91]
, [stateAt 133, stateAt 82, stateAt 19]
, [stateAt 133, stateAt 83, stateAt 27]
, [stateAt 133, stateAt 102, stateAt 67]
, [stateAt 133, stateAt 103, stateAt 75]
, [stateAt 134, stateAt 72, stateAt 83]
, [stateAt 134, stateAt 73, stateAt 91]
, [stateAt 134, stateAt 74, stateAt 19]
, [stateAt 134, stateAt 75, stateAt 27]
, [stateAt 134, stateAt 126, stateAt 67]
, [stateAt 134, stateAt 127, stateAt 75]
, [stateAt 135, stateAt 64, stateAt 83]
, [stateAt 135, stateAt 65, stateAt 91]
, [stateAt 135, stateAt 66, stateAt 19]
, [stateAt 135, stateAt 67, stateAt 27]
, [stateAt 135, stateAt 118, stateAt 67]
, [stateAt 135, stateAt 119, stateAt 75]
]
, []
, []
, [
  [stateAt 180, stateAt 24, stateAt 83]
, [stateAt 180, stateAt 25, stateAt 91]
, [stateAt 180, stateAt 26, stateAt 19]
, [stateAt 180, stateAt 27, stateAt 27]
, [stateAt 180, stateAt 42, stateAt 3]
, [stateAt 180, stateAt 43, stateAt 11]
, [stateAt 181, stateAt 16, stateAt 83]
, [stateAt 181, stateAt 17, stateAt 91]
, [stateAt 181, stateAt 18, stateAt 19]
, [stateAt 181, stateAt 19, stateAt 27]
, [stateAt 181, stateAt 34, stateAt 3]
, [stateAt 181, stateAt 35, stateAt 11]
, [stateAt 182, stateAt 8, stateAt 83]
, [stateAt 182, stateAt 9, stateAt 91]
, [stateAt 182, stateAt 10, stateAt 19]
, [stateAt 182, stateAt 11, stateAt 27]
, [stateAt 182, stateAt 58, stateAt 3]
, [stateAt 182, stateAt 59, stateAt 11]
, [stateAt 183, stateAt 0, stateAt 83]
, [stateAt 183, stateAt 1, stateAt 91]
, [stateAt 183, stateAt 2, stateAt 19]
, [stateAt 183, stateAt 3, stateAt 27]
, [stateAt 183, stateAt 50, stateAt 3]
, [stateAt 183, stateAt 51, stateAt 11]
]
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
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.r, LColor.r, LColor.p, LColor.p]
  exact hfast.trans fiber8_keyed_eq

def cert8 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.r, LColor.p, LColor.p],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 0, 1, 1, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 24, 25, 26, 27, 28, 29, 18, 19, 20, 21, 22, 23] }

def cert8_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert8_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert8_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert8_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_0 = cert8_layer_0_1_0 := by
  decide

def cert8_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_layer_0_1_1 : List ChainEdge :=
  []

theorem cert8_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_1_1 = cert8_layer_0_1_1 := by
  decide

theorem cert8_component_0_1_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert8_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
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

def cert8_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_0 = cert8_layer_0_2_0 := by
  decide

def cert8_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_0_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_1 = cert8_layer_0_2_1 := by
  decide

def cert8_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_0_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_2 = cert8_layer_0_2_2 := by
  decide

def cert8_seen_0_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_0_2_3 : List ChainEdge :=
  []

theorem cert8_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_2_3 = cert8_layer_0_2_3 := by
  decide

theorem cert8_component_0_2_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert8_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 27 cert8_seen_0_2_0 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_0 cert8_layer_0_2_0 26 cert8_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 26 cert8_seen_0_2_1 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_1 cert8_layer_0_2_1 25 cert8_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 25 cert8_seen_0_2_2 = cert8_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_2 cert8_layer_0_2_2 24 cert8_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 24 cert8_seen_0_2_3 = cert8_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_2_3 cert8_layer_0_2_3_eq 24

theorem cert8_step_0_2 :
    closedCollarIndexStepBool word fiber8 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_2)
    (by decide) (by decide)
    (by simpa [cert8_move_0_2] using cert8_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_0_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_seen_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_5_0 = cert8_layer_0_5_0 := by
  decide

def cert8_seen_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_5_1 = cert8_layer_0_5_1 := by
  decide

def cert8_seen_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert8_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_5_2 = cert8_layer_0_5_2 := by
  decide

def cert8_seen_0_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_layer_0_5_3 : List ChainEdge :=
  []

theorem cert8_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_5_3 = cert8_layer_0_5_3 := by
  decide

theorem cert8_component_0_5_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert8_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 27 cert8_seen_0_5_0 = cert8_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_5_0 cert8_layer_0_5_0 26 cert8_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 26 cert8_seen_0_5_1 = cert8_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_5_1 cert8_layer_0_5_1 25 cert8_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 25 cert8_seen_0_5_2 = cert8_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_5_2 cert8_layer_0_5_2 24 cert8_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 24 cert8_seen_0_5_3 = cert8_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_5_3 cert8_layer_0_5_3_eq 24

theorem cert8_step_0_5 :
    closedCollarIndexStepBool word fiber8 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_5)
    (by decide) (by decide)
    (by simpa [cert8_move_0_5] using cert8_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_6_0 = cert8_layer_0_6_0 := by
  decide

def cert8_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_0_6_1 : List ChainEdge :=
  []

theorem cert8_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.b LColor.p cert8_seen_0_6_1 = cert8_layer_0_6_1 := by
  decide

theorem cert8_component_0_6_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 27 cert8_seen_0_6_0 = cert8_component_0_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_6_0 cert8_layer_0_6_0 26 cert8_layer_0_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.b LColor.p 26 cert8_seen_0_6_1 = cert8_component_0_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.b LColor.p
    cert8_seen_0_6_1 cert8_layer_0_6_1_eq 26

theorem cert8_step_0_6 :
    closedCollarIndexStepBool word fiber8 0 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_6)
    (by decide) (by decide)
    (by simpa [cert8_move_0_6] using cert8_component_0_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_18 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_0_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_0_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_0_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_0_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_18_0 = cert8_layer_0_18_0 := by
  decide

def cert8_seen_0_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_0_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_18_1 = cert8_layer_0_18_1 := by
  decide

def cert8_seen_0_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_0_18_2 : List ChainEdge :=
  []

theorem cert8_layer_0_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.p cert8_seen_0_18_2 = cert8_layer_0_18_2 := by
  decide

theorem cert8_component_0_18_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_0_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 27 cert8_seen_0_18_0 = cert8_component_0_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_18_0 cert8_layer_0_18_0 26 cert8_layer_0_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 26 cert8_seen_0_18_1 = cert8_component_0_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_18_1 cert8_layer_0_18_1 25 cert8_layer_0_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.p 25 cert8_seen_0_18_2 = cert8_component_0_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.p
    cert8_seen_0_18_2 cert8_layer_0_18_2_eq 25

theorem cert8_step_0_18 :
    closedCollarIndexStepBool word fiber8 0 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_18)
    (by decide) (by decide)
    (by simpa [cert8_move_0_18] using cert8_component_0_18_eq)
    (by decide) (by decide) (by decide)

def cert8_move_0_24 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_0_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_0_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_24_0 = cert8_layer_0_24_0 := by
  decide

def cert8_seen_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_0_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_24_1 = cert8_layer_0_24_1 := by
  decide

def cert8_seen_0_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_0_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_0_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_24_2 = cert8_layer_0_24_2 := by
  decide

def cert8_seen_0_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_0_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_0_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_24_3 = cert8_layer_0_24_3 := by
  decide

def cert8_seen_0_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_0_24_4 : List ChainEdge :=
  []

theorem cert8_layer_0_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 0 [])
      LColor.r LColor.b cert8_seen_0_24_4 = cert8_layer_0_24_4 := by
  decide

theorem cert8_component_0_24_eq :
    closedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_0_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 27 cert8_seen_0_24_0 = cert8_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_24_0 cert8_layer_0_24_0 26 cert8_layer_0_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 26 cert8_seen_0_24_1 = cert8_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_24_1 cert8_layer_0_24_1 25 cert8_layer_0_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 25 cert8_seen_0_24_2 = cert8_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_24_2 cert8_layer_0_24_2 24 cert8_layer_0_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 24 cert8_seen_0_24_3 = cert8_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_24_3 cert8_layer_0_24_3 23 cert8_layer_0_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 0 [])
      LColor.r LColor.b 23 cert8_seen_0_24_4 = cert8_component_0_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 0 []) LColor.r LColor.b
    cert8_seen_0_24_4 cert8_layer_0_24_4_eq 23

theorem cert8_step_0_24 :
    closedCollarIndexStepBool word fiber8 0 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_0_24)
    (by decide) (by decide)
    (by simpa [cert8_move_0_24] using cert8_component_0_24_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert8_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert8_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert8_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_0 = cert8_layer_1_0_0 := by
  decide

def cert8_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_layer_1_0_1 : List ChainEdge :=
  []

theorem cert8_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_0_1 = cert8_layer_1_0_1 := by
  decide

theorem cert8_component_1_0_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert8_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
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

def cert8_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_0 = cert8_layer_1_3_0 := by
  decide

def cert8_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_1_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_1 = cert8_layer_1_3_1 := by
  decide

def cert8_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_1_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_2 = cert8_layer_1_3_2 := by
  decide

def cert8_seen_1_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_1_3_3 : List ChainEdge :=
  []

theorem cert8_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_3_3 = cert8_layer_1_3_3 := by
  decide

theorem cert8_component_1_3_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert8_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 27 cert8_seen_1_3_0 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_0 cert8_layer_1_3_0 26 cert8_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 26 cert8_seen_1_3_1 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_1 cert8_layer_1_3_1 25 cert8_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 25 cert8_seen_1_3_2 = cert8_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_2 cert8_layer_1_3_2 24 cert8_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 24 cert8_seen_1_3_3 = cert8_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_3_3 cert8_layer_1_3_3_eq 24

theorem cert8_step_1_3 :
    closedCollarIndexStepBool word fiber8 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_3)
    (by decide) (by decide)
    (by simpa [cert8_move_1_3] using cert8_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_seen_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_4_0 = cert8_layer_1_4_0 := by
  decide

def cert8_seen_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_4_1 = cert8_layer_1_4_1 := by
  decide

def cert8_seen_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert8_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_4_2 = cert8_layer_1_4_2 := by
  decide

def cert8_seen_1_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_layer_1_4_3 : List ChainEdge :=
  []

theorem cert8_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_4_3 = cert8_layer_1_4_3 := by
  decide

theorem cert8_component_1_4_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert8_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 27 cert8_seen_1_4_0 = cert8_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_4_0 cert8_layer_1_4_0 26 cert8_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 26 cert8_seen_1_4_1 = cert8_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_4_1 cert8_layer_1_4_1 25 cert8_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 25 cert8_seen_1_4_2 = cert8_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_4_2 cert8_layer_1_4_2 24 cert8_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 24 cert8_seen_1_4_3 = cert8_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_4_3 cert8_layer_1_4_3_eq 24

theorem cert8_step_1_4 :
    closedCollarIndexStepBool word fiber8 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_4)
    (by decide) (by decide)
    (by simpa [cert8_move_1_4] using cert8_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_7_0 = cert8_layer_1_7_0 := by
  decide

def cert8_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_1_7_1 : List ChainEdge :=
  []

theorem cert8_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.b LColor.p cert8_seen_1_7_1 = cert8_layer_1_7_1 := by
  decide

theorem cert8_component_1_7_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 27 cert8_seen_1_7_0 = cert8_component_1_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_7_0 cert8_layer_1_7_0 26 cert8_layer_1_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.b LColor.p 26 cert8_seen_1_7_1 = cert8_component_1_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.b LColor.p
    cert8_seen_1_7_1 cert8_layer_1_7_1_eq 26

theorem cert8_step_1_7 :
    closedCollarIndexStepBool word fiber8 1 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_7)
    (by decide) (by decide)
    (by simpa [cert8_move_1_7] using cert8_component_1_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_19 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_1_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_1_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_1_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_1_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_19_0 = cert8_layer_1_19_0 := by
  decide

def cert8_seen_1_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_1_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_19_1 = cert8_layer_1_19_1 := by
  decide

def cert8_seen_1_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_1_19_2 : List ChainEdge :=
  []

theorem cert8_layer_1_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.p cert8_seen_1_19_2 = cert8_layer_1_19_2 := by
  decide

theorem cert8_component_1_19_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_1_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 27 cert8_seen_1_19_0 = cert8_component_1_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_19_0 cert8_layer_1_19_0 26 cert8_layer_1_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 26 cert8_seen_1_19_1 = cert8_component_1_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_19_1 cert8_layer_1_19_1 25 cert8_layer_1_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.p 25 cert8_seen_1_19_2 = cert8_component_1_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.p
    cert8_seen_1_19_2 cert8_layer_1_19_2_eq 25

theorem cert8_step_1_19 :
    closedCollarIndexStepBool word fiber8 1 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_19)
    (by decide) (by decide)
    (by simpa [cert8_move_1_19] using cert8_component_1_19_eq)
    (by decide) (by decide) (by decide)

def cert8_move_1_25 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_1_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_1_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_25_0 = cert8_layer_1_25_0 := by
  decide

def cert8_seen_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_1_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_25_1 = cert8_layer_1_25_1 := by
  decide

def cert8_seen_1_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_1_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_1_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_25_2 = cert8_layer_1_25_2 := by
  decide

def cert8_seen_1_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_1_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_1_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_25_3 = cert8_layer_1_25_3 := by
  decide

def cert8_seen_1_25_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_1_25_4 : List ChainEdge :=
  []

theorem cert8_layer_1_25_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 1 [])
      LColor.r LColor.b cert8_seen_1_25_4 = cert8_layer_1_25_4 := by
  decide

theorem cert8_component_1_25_eq :
    closedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_1_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 27 cert8_seen_1_25_0 = cert8_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_25_0 cert8_layer_1_25_0 26 cert8_layer_1_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 26 cert8_seen_1_25_1 = cert8_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_25_1 cert8_layer_1_25_1 25 cert8_layer_1_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 25 cert8_seen_1_25_2 = cert8_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_25_2 cert8_layer_1_25_2 24 cert8_layer_1_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 24 cert8_seen_1_25_3 = cert8_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_25_3 cert8_layer_1_25_3 23 cert8_layer_1_25_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 1 [])
      LColor.r LColor.b 23 cert8_seen_1_25_4 = cert8_component_1_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 1 []) LColor.r LColor.b
    cert8_seen_1_25_4 cert8_layer_1_25_4_eq 23

theorem cert8_step_1_25 :
    closedCollarIndexStepBool word fiber8 1 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_1_25)
    (by decide) (by decide)
    (by simpa [cert8_move_1_25] using cert8_component_1_25_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_0 = cert8_layer_2_0_0 := by
  decide

def cert8_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_2_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_1 = cert8_layer_2_0_1 := by
  decide

def cert8_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_2_0_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_2 = cert8_layer_2_0_2 := by
  decide

def cert8_seen_2_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_2_0_3 : List ChainEdge :=
  []

theorem cert8_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_0_3 = cert8_layer_2_0_3 := by
  decide

theorem cert8_component_2_0_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert8_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 27 cert8_seen_2_0_0 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_0 cert8_layer_2_0_0 26 cert8_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 26 cert8_seen_2_0_1 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_1 cert8_layer_2_0_1 25 cert8_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 25 cert8_seen_2_0_2 = cert8_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_2 cert8_layer_2_0_2 24 cert8_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 24 cert8_seen_2_0_3 = cert8_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_0_3 cert8_layer_2_0_3_eq 24

theorem cert8_step_2_0 :
    closedCollarIndexStepBool word fiber8 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_0)
    (by decide) (by decide)
    (by simpa [cert8_move_2_0] using cert8_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_8_0 = cert8_layer_2_8_0 := by
  decide

def cert8_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_2_8_1 : List ChainEdge :=
  []

theorem cert8_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.b LColor.p cert8_seen_2_8_1 = cert8_layer_2_8_1 := by
  decide

theorem cert8_component_2_8_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 27 cert8_seen_2_8_0 = cert8_component_2_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_8_0 cert8_layer_2_8_0 26 cert8_layer_2_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.b LColor.p 26 cert8_seen_2_8_1 = cert8_component_2_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.b LColor.p
    cert8_seen_2_8_1 cert8_layer_2_8_1_eq 26

theorem cert8_step_2_8 :
    closedCollarIndexStepBool word fiber8 2 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_8)
    (by decide) (by decide)
    (by simpa [cert8_move_2_8] using cert8_component_2_8_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_20 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_2_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_2_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_2_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_2_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_20_0 = cert8_layer_2_20_0 := by
  decide

def cert8_seen_2_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_2_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_2_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_20_1 = cert8_layer_2_20_1 := by
  decide

def cert8_seen_2_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_2_20_2 : List ChainEdge :=
  []

theorem cert8_layer_2_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.p cert8_seen_2_20_2 = cert8_layer_2_20_2 := by
  decide

theorem cert8_component_2_20_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_2_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 27 cert8_seen_2_20_0 = cert8_component_2_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_20_0 cert8_layer_2_20_0 26 cert8_layer_2_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 26 cert8_seen_2_20_1 = cert8_component_2_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_20_1 cert8_layer_2_20_1 25 cert8_layer_2_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.p 25 cert8_seen_2_20_2 = cert8_component_2_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.p
    cert8_seen_2_20_2 cert8_layer_2_20_2_eq 25

theorem cert8_step_2_20 :
    closedCollarIndexStepBool word fiber8 2 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_20)
    (by decide) (by decide)
    (by simpa [cert8_move_2_20] using cert8_component_2_20_eq)
    (by decide) (by decide) (by decide)

def cert8_move_2_26 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_2_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_2_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_26_0 = cert8_layer_2_26_0 := by
  decide

def cert8_seen_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_2_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_26_1 = cert8_layer_2_26_1 := by
  decide

def cert8_seen_2_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_2_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_2_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_26_2 = cert8_layer_2_26_2 := by
  decide

def cert8_seen_2_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_2_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_2_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_26_3 = cert8_layer_2_26_3 := by
  decide

def cert8_seen_2_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_2_26_4 : List ChainEdge :=
  []

theorem cert8_layer_2_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 2 [])
      LColor.r LColor.b cert8_seen_2_26_4 = cert8_layer_2_26_4 := by
  decide

theorem cert8_component_2_26_eq :
    closedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_2_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 27 cert8_seen_2_26_0 = cert8_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_26_0 cert8_layer_2_26_0 26 cert8_layer_2_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 26 cert8_seen_2_26_1 = cert8_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_26_1 cert8_layer_2_26_1 25 cert8_layer_2_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 25 cert8_seen_2_26_2 = cert8_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_26_2 cert8_layer_2_26_2 24 cert8_layer_2_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 24 cert8_seen_2_26_3 = cert8_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_26_3 cert8_layer_2_26_3 23 cert8_layer_2_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 2 [])
      LColor.r LColor.b 23 cert8_seen_2_26_4 = cert8_component_2_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 2 []) LColor.r LColor.b
    cert8_seen_2_26_4 cert8_layer_2_26_4_eq 23

theorem cert8_step_2_26 :
    closedCollarIndexStepBool word fiber8 2 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_2_26)
    (by decide) (by decide)
    (by simpa [cert8_move_2_26] using cert8_component_2_26_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert8_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert8_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_0 = cert8_layer_3_1_0 := by
  decide

def cert8_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_3_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_1 = cert8_layer_3_1_1 := by
  decide

def cert8_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_3_1_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_2 = cert8_layer_3_1_2 := by
  decide

def cert8_seen_3_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_3_1_3 : List ChainEdge :=
  []

theorem cert8_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_1_3 = cert8_layer_3_1_3 := by
  decide

theorem cert8_component_3_1_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert8_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 27 cert8_seen_3_1_0 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_0 cert8_layer_3_1_0 26 cert8_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 26 cert8_seen_3_1_1 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_1 cert8_layer_3_1_1 25 cert8_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 25 cert8_seen_3_1_2 = cert8_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_2 cert8_layer_3_1_2 24 cert8_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 24 cert8_seen_3_1_3 = cert8_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_1_3 cert8_layer_3_1_3_eq 24

theorem cert8_step_3_1 :
    closedCollarIndexStepBool word fiber8 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_1)
    (by decide) (by decide)
    (by simpa [cert8_move_3_1] using cert8_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_9_0 = cert8_layer_3_9_0 := by
  decide

def cert8_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_3_9_1 : List ChainEdge :=
  []

theorem cert8_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.b LColor.p cert8_seen_3_9_1 = cert8_layer_3_9_1 := by
  decide

theorem cert8_component_3_9_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 27 cert8_seen_3_9_0 = cert8_component_3_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_9_0 cert8_layer_3_9_0 26 cert8_layer_3_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.b LColor.p 26 cert8_seen_3_9_1 = cert8_component_3_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.b LColor.p
    cert8_seen_3_9_1 cert8_layer_3_9_1_eq 26

theorem cert8_step_3_9 :
    closedCollarIndexStepBool word fiber8 3 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_9)
    (by decide) (by decide)
    (by simpa [cert8_move_3_9] using cert8_component_3_9_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_21 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_3_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_3_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_3_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_3_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_21_0 = cert8_layer_3_21_0 := by
  decide

def cert8_seen_3_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_3_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_3_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_21_1 = cert8_layer_3_21_1 := by
  decide

def cert8_seen_3_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_3_21_2 : List ChainEdge :=
  []

theorem cert8_layer_3_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.p cert8_seen_3_21_2 = cert8_layer_3_21_2 := by
  decide

theorem cert8_component_3_21_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_3_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 27 cert8_seen_3_21_0 = cert8_component_3_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_21_0 cert8_layer_3_21_0 26 cert8_layer_3_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 26 cert8_seen_3_21_1 = cert8_component_3_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_21_1 cert8_layer_3_21_1 25 cert8_layer_3_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.p 25 cert8_seen_3_21_2 = cert8_component_3_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.p
    cert8_seen_3_21_2 cert8_layer_3_21_2_eq 25

theorem cert8_step_3_21 :
    closedCollarIndexStepBool word fiber8 3 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_21)
    (by decide) (by decide)
    (by simpa [cert8_move_3_21] using cert8_component_3_21_eq)
    (by decide) (by decide) (by decide)

def cert8_move_3_27 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_3_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_3_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_27_0 = cert8_layer_3_27_0 := by
  decide

def cert8_seen_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_3_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_27_1 = cert8_layer_3_27_1 := by
  decide

def cert8_seen_3_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_3_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_3_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_27_2 = cert8_layer_3_27_2 := by
  decide

def cert8_seen_3_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_3_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_3_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_27_3 = cert8_layer_3_27_3 := by
  decide

def cert8_seen_3_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_3_27_4 : List ChainEdge :=
  []

theorem cert8_layer_3_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 3 [])
      LColor.r LColor.b cert8_seen_3_27_4 = cert8_layer_3_27_4 := by
  decide

theorem cert8_component_3_27_eq :
    closedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_3_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 27 cert8_seen_3_27_0 = cert8_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_27_0 cert8_layer_3_27_0 26 cert8_layer_3_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 26 cert8_seen_3_27_1 = cert8_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_27_1 cert8_layer_3_27_1 25 cert8_layer_3_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 25 cert8_seen_3_27_2 = cert8_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_27_2 cert8_layer_3_27_2 24 cert8_layer_3_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 24 cert8_seen_3_27_3 = cert8_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_27_3 cert8_layer_3_27_3 23 cert8_layer_3_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 3 [])
      LColor.r LColor.b 23 cert8_seen_3_27_4 = cert8_component_3_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 3 []) LColor.r LColor.b
    cert8_seen_3_27_4 cert8_layer_3_27_4_eq 23

theorem cert8_step_3_27 :
    closedCollarIndexStepBool word fiber8 3 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_3_27)
    (by decide) (by decide)
    (by simpa [cert8_move_3_27] using cert8_component_3_27_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_seen_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_1_0 = cert8_layer_4_1_0 := by
  decide

def cert8_seen_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_1_1 = cert8_layer_4_1_1 := by
  decide

def cert8_seen_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert8_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_1_2 = cert8_layer_4_1_2 := by
  decide

def cert8_seen_4_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert8_layer_4_1_3 : List ChainEdge :=
  []

theorem cert8_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_1_3 = cert8_layer_4_1_3 := by
  decide

theorem cert8_component_4_1_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert8_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 27 cert8_seen_4_1_0 = cert8_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_1_0 cert8_layer_4_1_0 26 cert8_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 26 cert8_seen_4_1_1 = cert8_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_1_1 cert8_layer_4_1_1 25 cert8_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 25 cert8_seen_4_1_2 = cert8_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_1_2 cert8_layer_4_1_2 24 cert8_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 24 cert8_seen_4_1_3 = cert8_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_1_3 cert8_layer_4_1_3_eq 24

theorem cert8_step_4_1 :
    closedCollarIndexStepBool word fiber8 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_1)
    (by decide) (by decide)
    (by simpa [cert8_move_4_1] using cert8_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_10_0 = cert8_layer_4_10_0 := by
  decide

def cert8_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_4_10_1 : List ChainEdge :=
  []

theorem cert8_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.b LColor.p cert8_seen_4_10_1 = cert8_layer_4_10_1 := by
  decide

theorem cert8_component_4_10_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 27 cert8_seen_4_10_0 = cert8_component_4_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_10_0 cert8_layer_4_10_0 26 cert8_layer_4_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.b LColor.p 26 cert8_seen_4_10_1 = cert8_component_4_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.b LColor.p
    cert8_seen_4_10_1 cert8_layer_4_10_1_eq 26

theorem cert8_step_4_10 :
    closedCollarIndexStepBool word fiber8 4 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_10)
    (by decide) (by decide)
    (by simpa [cert8_move_4_10] using cert8_component_4_10_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_22 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_4_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_4_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_4_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_4_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_22_0 = cert8_layer_4_22_0 := by
  decide

def cert8_seen_4_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_4_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_4_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_22_1 = cert8_layer_4_22_1 := by
  decide

def cert8_seen_4_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_4_22_2 : List ChainEdge :=
  []

theorem cert8_layer_4_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.p cert8_seen_4_22_2 = cert8_layer_4_22_2 := by
  decide

theorem cert8_component_4_22_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_4_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 27 cert8_seen_4_22_0 = cert8_component_4_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_22_0 cert8_layer_4_22_0 26 cert8_layer_4_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 26 cert8_seen_4_22_1 = cert8_component_4_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_22_1 cert8_layer_4_22_1 25 cert8_layer_4_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.p 25 cert8_seen_4_22_2 = cert8_component_4_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.r LColor.p
    cert8_seen_4_22_2 cert8_layer_4_22_2_eq 25

theorem cert8_step_4_22 :
    closedCollarIndexStepBool word fiber8 4 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_22)
    (by decide) (by decide)
    (by simpa [cert8_move_4_22] using cert8_component_4_22_eq)
    (by decide) (by decide) (by decide)

def cert8_move_4_28 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_4_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_4_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_4_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_4_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_0 = cert8_layer_4_28_0 := by
  decide

def cert8_seen_4_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_4_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_4_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_1 = cert8_layer_4_28_1 := by
  decide

def cert8_seen_4_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_4_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_4_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_2 = cert8_layer_4_28_2 := by
  decide

def cert8_seen_4_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_4_28_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_4_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_3 = cert8_layer_4_28_3 := by
  decide

def cert8_seen_4_28_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_4_28_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_4_28_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_4 = cert8_layer_4_28_4 := by
  decide

def cert8_seen_4_28_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_4_28_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_4_28_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_5 = cert8_layer_4_28_5 := by
  decide

def cert8_seen_4_28_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_4_28_6 : List ChainEdge :=
  []

theorem cert8_layer_4_28_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 4 [])
      LColor.r LColor.b cert8_seen_4_28_6 = cert8_layer_4_28_6 := by
  decide

theorem cert8_component_4_28_eq :
    closedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_4_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 27 cert8_seen_4_28_0 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_0 cert8_layer_4_28_0 26 cert8_layer_4_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 26 cert8_seen_4_28_1 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_1 cert8_layer_4_28_1 25 cert8_layer_4_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 25 cert8_seen_4_28_2 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_2 cert8_layer_4_28_2 24 cert8_layer_4_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 24 cert8_seen_4_28_3 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_3 cert8_layer_4_28_3 23 cert8_layer_4_28_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 23 cert8_seen_4_28_4 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_4 cert8_layer_4_28_4 22 cert8_layer_4_28_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 22 cert8_seen_4_28_5 = cert8_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_5 cert8_layer_4_28_5 21 cert8_layer_4_28_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 4 [])
      LColor.r LColor.b 21 cert8_seen_4_28_6 = cert8_component_4_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 4 []) LColor.r LColor.b
    cert8_seen_4_28_6 cert8_layer_4_28_6_eq 21

theorem cert8_step_4_28 :
    closedCollarIndexStepBool word fiber8 4 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_4_28)
    (by decide) (by decide)
    (by simpa [cert8_move_4_28] using cert8_component_4_28_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert8_component_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_seen_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_0_0 = cert8_layer_5_0_0 := by
  decide

def cert8_seen_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert8_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_0_1 = cert8_layer_5_0_1 := by
  decide

def cert8_seen_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert8_layer_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert8_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_0_2 = cert8_layer_5_0_2 := by
  decide

def cert8_seen_5_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert8_layer_5_0_3 : List ChainEdge :=
  []

theorem cert8_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_0_3 = cert8_layer_5_0_3 := by
  decide

theorem cert8_component_5_0_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert8_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 27 cert8_seen_5_0_0 = cert8_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_0_0 cert8_layer_5_0_0 26 cert8_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 26 cert8_seen_5_0_1 = cert8_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_0_1 cert8_layer_5_0_1 25 cert8_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 25 cert8_seen_5_0_2 = cert8_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_0_2 cert8_layer_5_0_2 24 cert8_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 24 cert8_seen_5_0_3 = cert8_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_0_3 cert8_layer_5_0_3_eq 24

theorem cert8_step_5_0 :
    closedCollarIndexStepBool word fiber8 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_0)
    (by decide) (by decide)
    (by simpa [cert8_move_5_0] using cert8_component_5_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_11_0 = cert8_layer_5_11_0 := by
  decide

def cert8_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_5_11_1 : List ChainEdge :=
  []

theorem cert8_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.b LColor.p cert8_seen_5_11_1 = cert8_layer_5_11_1 := by
  decide

theorem cert8_component_5_11_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 27 cert8_seen_5_11_0 = cert8_component_5_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_11_0 cert8_layer_5_11_0 26 cert8_layer_5_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.b LColor.p 26 cert8_seen_5_11_1 = cert8_component_5_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.b LColor.p
    cert8_seen_5_11_1 cert8_layer_5_11_1_eq 26

theorem cert8_step_5_11 :
    closedCollarIndexStepBool word fiber8 5 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_11)
    (by decide) (by decide)
    (by simpa [cert8_move_5_11] using cert8_component_5_11_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_23 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_5_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_5_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_5_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_5_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_23_0 = cert8_layer_5_23_0 := by
  decide

def cert8_seen_5_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_5_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_5_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_23_1 = cert8_layer_5_23_1 := by
  decide

def cert8_seen_5_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_5_23_2 : List ChainEdge :=
  []

theorem cert8_layer_5_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.p cert8_seen_5_23_2 = cert8_layer_5_23_2 := by
  decide

theorem cert8_component_5_23_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_5_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 27 cert8_seen_5_23_0 = cert8_component_5_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_23_0 cert8_layer_5_23_0 26 cert8_layer_5_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 26 cert8_seen_5_23_1 = cert8_component_5_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_23_1 cert8_layer_5_23_1 25 cert8_layer_5_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.p 25 cert8_seen_5_23_2 = cert8_component_5_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.r LColor.p
    cert8_seen_5_23_2 cert8_layer_5_23_2_eq 25

theorem cert8_step_5_23 :
    closedCollarIndexStepBool word fiber8 5 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_23)
    (by decide) (by decide)
    (by simpa [cert8_move_5_23] using cert8_component_5_23_eq)
    (by decide) (by decide) (by decide)

def cert8_move_5_29 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_5_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_5_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_5_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_5_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_0 = cert8_layer_5_29_0 := by
  decide

def cert8_seen_5_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_5_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_5_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_1 = cert8_layer_5_29_1 := by
  decide

def cert8_seen_5_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_5_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_5_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_2 = cert8_layer_5_29_2 := by
  decide

def cert8_seen_5_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_5_29_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_5_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_3 = cert8_layer_5_29_3 := by
  decide

def cert8_seen_5_29_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_5_29_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_5_29_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_4 = cert8_layer_5_29_4 := by
  decide

def cert8_seen_5_29_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_5_29_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_5_29_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_5 = cert8_layer_5_29_5 := by
  decide

def cert8_seen_5_29_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_5_29_6 : List ChainEdge :=
  []

theorem cert8_layer_5_29_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 5 [])
      LColor.r LColor.b cert8_seen_5_29_6 = cert8_layer_5_29_6 := by
  decide

theorem cert8_component_5_29_eq :
    closedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_5_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 27 cert8_seen_5_29_0 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_0 cert8_layer_5_29_0 26 cert8_layer_5_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 26 cert8_seen_5_29_1 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_1 cert8_layer_5_29_1 25 cert8_layer_5_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 25 cert8_seen_5_29_2 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_2 cert8_layer_5_29_2 24 cert8_layer_5_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 24 cert8_seen_5_29_3 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_3 cert8_layer_5_29_3 23 cert8_layer_5_29_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 23 cert8_seen_5_29_4 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_4 cert8_layer_5_29_4 22 cert8_layer_5_29_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 22 cert8_seen_5_29_5 = cert8_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_5 cert8_layer_5_29_5 21 cert8_layer_5_29_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 5 [])
      LColor.r LColor.b 21 cert8_seen_5_29_6 = cert8_component_5_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 5 []) LColor.r LColor.b
    cert8_seen_5_29_6 cert8_layer_5_29_6_eq 21

theorem cert8_step_5_29 :
    closedCollarIndexStepBool word fiber8 5 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_5_29)
    (by decide) (by decide)
    (by simpa [cert8_move_5_29] using cert8_component_5_29_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_0_0 = cert8_layer_6_0_0 := by
  decide

def cert8_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_6_0_1 : List ChainEdge :=
  []

theorem cert8_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.b LColor.p cert8_seen_6_0_1 = cert8_layer_6_0_1 := by
  decide

theorem cert8_component_6_0_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 27 cert8_seen_6_0_0 = cert8_component_6_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_0_0 cert8_layer_6_0_0 26 cert8_layer_6_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.b LColor.p 26 cert8_seen_6_0_1 = cert8_component_6_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.b LColor.p
    cert8_seen_6_0_1 cert8_layer_6_0_1_eq 26

theorem cert8_step_6_0 :
    closedCollarIndexStepBool word fiber8 6 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_0)
    (by decide) (by decide)
    (by simpa [cert8_move_6_0] using cert8_component_6_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_6_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_6_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_6_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_6_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.p cert8_seen_6_12_0 = cert8_layer_6_12_0 := by
  decide

def cert8_seen_6_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_6_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_6_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.p cert8_seen_6_12_1 = cert8_layer_6_12_1 := by
  decide

def cert8_seen_6_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_6_12_2 : List ChainEdge :=
  []

theorem cert8_layer_6_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.p cert8_seen_6_12_2 = cert8_layer_6_12_2 := by
  decide

theorem cert8_component_6_12_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_6_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.p 27 cert8_seen_6_12_0 = cert8_component_6_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.p
    cert8_seen_6_12_0 cert8_layer_6_12_0 26 cert8_layer_6_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.p 26 cert8_seen_6_12_1 = cert8_component_6_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.p
    cert8_seen_6_12_1 cert8_layer_6_12_1 25 cert8_layer_6_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.p 25 cert8_seen_6_12_2 = cert8_component_6_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.r LColor.p
    cert8_seen_6_12_2 cert8_layer_6_12_2_eq 25

theorem cert8_step_6_12 :
    closedCollarIndexStepBool word fiber8 6 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_12)
    (by decide) (by decide)
    (by simpa [cert8_move_6_12] using cert8_component_6_12_eq)
    (by decide) (by decide) (by decide)

def cert8_move_6_30 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_6_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_6_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_30_0 = cert8_layer_6_30_0 := by
  decide

def cert8_seen_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_6_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_30_1 = cert8_layer_6_30_1 := by
  decide

def cert8_seen_6_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_6_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_6_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_30_2 = cert8_layer_6_30_2 := by
  decide

def cert8_seen_6_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_6_30_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_6_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_30_3 = cert8_layer_6_30_3 := by
  decide

def cert8_seen_6_30_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_6_30_4 : List ChainEdge :=
  []

theorem cert8_layer_6_30_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 6 [])
      LColor.r LColor.b cert8_seen_6_30_4 = cert8_layer_6_30_4 := by
  decide

theorem cert8_component_6_30_eq :
    closedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_6_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 27 cert8_seen_6_30_0 = cert8_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_30_0 cert8_layer_6_30_0 26 cert8_layer_6_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 26 cert8_seen_6_30_1 = cert8_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_30_1 cert8_layer_6_30_1 25 cert8_layer_6_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 25 cert8_seen_6_30_2 = cert8_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_30_2 cert8_layer_6_30_2 24 cert8_layer_6_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 24 cert8_seen_6_30_3 = cert8_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_30_3 cert8_layer_6_30_3 23 cert8_layer_6_30_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 6 [])
      LColor.r LColor.b 23 cert8_seen_6_30_4 = cert8_component_6_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 6 []) LColor.r LColor.b
    cert8_seen_6_30_4 cert8_layer_6_30_4_eq 23

theorem cert8_step_6_30 :
    closedCollarIndexStepBool word fiber8 6 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_6_30)
    (by decide) (by decide)
    (by simpa [cert8_move_6_30] using cert8_component_6_30_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_1_0 = cert8_layer_7_1_0 := by
  decide

def cert8_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_7_1_1 : List ChainEdge :=
  []

theorem cert8_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.b LColor.p cert8_seen_7_1_1 = cert8_layer_7_1_1 := by
  decide

theorem cert8_component_7_1_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 27 cert8_seen_7_1_0 = cert8_component_7_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_1_0 cert8_layer_7_1_0 26 cert8_layer_7_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.b LColor.p 26 cert8_seen_7_1_1 = cert8_component_7_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.b LColor.p
    cert8_seen_7_1_1 cert8_layer_7_1_1_eq 26

theorem cert8_step_7_1 :
    closedCollarIndexStepBool word fiber8 7 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_1)
    (by decide) (by decide)
    (by simpa [cert8_move_7_1] using cert8_component_7_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_7_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_7_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_7_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_7_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.p cert8_seen_7_13_0 = cert8_layer_7_13_0 := by
  decide

def cert8_seen_7_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_7_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_7_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.p cert8_seen_7_13_1 = cert8_layer_7_13_1 := by
  decide

def cert8_seen_7_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_7_13_2 : List ChainEdge :=
  []

theorem cert8_layer_7_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.p cert8_seen_7_13_2 = cert8_layer_7_13_2 := by
  decide

theorem cert8_component_7_13_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_7_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.p 27 cert8_seen_7_13_0 = cert8_component_7_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.p
    cert8_seen_7_13_0 cert8_layer_7_13_0 26 cert8_layer_7_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.p 26 cert8_seen_7_13_1 = cert8_component_7_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.p
    cert8_seen_7_13_1 cert8_layer_7_13_1 25 cert8_layer_7_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.p 25 cert8_seen_7_13_2 = cert8_component_7_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.r LColor.p
    cert8_seen_7_13_2 cert8_layer_7_13_2_eq 25

theorem cert8_step_7_13 :
    closedCollarIndexStepBool word fiber8 7 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_13)
    (by decide) (by decide)
    (by simpa [cert8_move_7_13] using cert8_component_7_13_eq)
    (by decide) (by decide) (by decide)

def cert8_move_7_31 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_7_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_7_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_31_0 = cert8_layer_7_31_0 := by
  decide

def cert8_seen_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_7_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_31_1 = cert8_layer_7_31_1 := by
  decide

def cert8_seen_7_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_7_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_7_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_31_2 = cert8_layer_7_31_2 := by
  decide

def cert8_seen_7_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_7_31_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_7_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_31_3 = cert8_layer_7_31_3 := by
  decide

def cert8_seen_7_31_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_7_31_4 : List ChainEdge :=
  []

theorem cert8_layer_7_31_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 7 [])
      LColor.r LColor.b cert8_seen_7_31_4 = cert8_layer_7_31_4 := by
  decide

theorem cert8_component_7_31_eq :
    closedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_7_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 27 cert8_seen_7_31_0 = cert8_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_31_0 cert8_layer_7_31_0 26 cert8_layer_7_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 26 cert8_seen_7_31_1 = cert8_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_31_1 cert8_layer_7_31_1 25 cert8_layer_7_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 25 cert8_seen_7_31_2 = cert8_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_31_2 cert8_layer_7_31_2 24 cert8_layer_7_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 24 cert8_seen_7_31_3 = cert8_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_31_3 cert8_layer_7_31_3 23 cert8_layer_7_31_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 7 [])
      LColor.r LColor.b 23 cert8_seen_7_31_4 = cert8_component_7_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 7 []) LColor.r LColor.b
    cert8_seen_7_31_4 cert8_layer_7_31_4_eq 23

theorem cert8_step_7_31 :
    closedCollarIndexStepBool word fiber8 7 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_7_31)
    (by decide) (by decide)
    (by simpa [cert8_move_7_31] using cert8_component_7_31_eq)
    (by decide) (by decide) (by decide)

def cert8_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.b LColor.p cert8_seen_8_2_0 = cert8_layer_8_2_0 := by
  decide

def cert8_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_8_2_1 : List ChainEdge :=
  []

theorem cert8_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.b LColor.p cert8_seen_8_2_1 = cert8_layer_8_2_1 := by
  decide

theorem cert8_component_8_2_eq :
    closedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p 27 cert8_seen_8_2_0 = cert8_component_8_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.b LColor.p
    cert8_seen_8_2_0 cert8_layer_8_2_0 26 cert8_layer_8_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.b LColor.p 26 cert8_seen_8_2_1 = cert8_component_8_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 8 []) LColor.b LColor.p
    cert8_seen_8_2_1 cert8_layer_8_2_1_eq 26

theorem cert8_step_8_2 :
    closedCollarIndexStepBool word fiber8 8 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_8_2)
    (by decide) (by decide)
    (by simpa [cert8_move_8_2] using cert8_component_8_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_8_14 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_8_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_8_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_8_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_8_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.p cert8_seen_8_14_0 = cert8_layer_8_14_0 := by
  decide

def cert8_seen_8_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_8_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_8_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.p cert8_seen_8_14_1 = cert8_layer_8_14_1 := by
  decide

def cert8_seen_8_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_8_14_2 : List ChainEdge :=
  []

theorem cert8_layer_8_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.p cert8_seen_8_14_2 = cert8_layer_8_14_2 := by
  decide

theorem cert8_component_8_14_eq :
    closedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_8_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.p 27 cert8_seen_8_14_0 = cert8_component_8_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.p
    cert8_seen_8_14_0 cert8_layer_8_14_0 26 cert8_layer_8_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.p 26 cert8_seen_8_14_1 = cert8_component_8_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.p
    cert8_seen_8_14_1 cert8_layer_8_14_1 25 cert8_layer_8_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.p 25 cert8_seen_8_14_2 = cert8_component_8_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 8 []) LColor.r LColor.p
    cert8_seen_8_14_2 cert8_layer_8_14_2_eq 25

theorem cert8_step_8_14 :
    closedCollarIndexStepBool word fiber8 8 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_8_14)
    (by decide) (by decide)
    (by simpa [cert8_move_8_14] using cert8_component_8_14_eq)
    (by decide) (by decide) (by decide)

def cert8_move_8_32 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_8_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_8_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_32_0 = cert8_layer_8_32_0 := by
  decide

def cert8_seen_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_8_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_32_1 = cert8_layer_8_32_1 := by
  decide

def cert8_seen_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_8_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_32_2 = cert8_layer_8_32_2 := by
  decide

def cert8_seen_8_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_8_32_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_8_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_32_3 = cert8_layer_8_32_3 := by
  decide

def cert8_seen_8_32_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_8_32_4 : List ChainEdge :=
  []

theorem cert8_layer_8_32_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 8 [])
      LColor.r LColor.b cert8_seen_8_32_4 = cert8_layer_8_32_4 := by
  decide

theorem cert8_component_8_32_eq :
    closedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_8_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 27 cert8_seen_8_32_0 = cert8_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_32_0 cert8_layer_8_32_0 26 cert8_layer_8_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 26 cert8_seen_8_32_1 = cert8_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_32_1 cert8_layer_8_32_1 25 cert8_layer_8_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 25 cert8_seen_8_32_2 = cert8_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_32_2 cert8_layer_8_32_2 24 cert8_layer_8_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 24 cert8_seen_8_32_3 = cert8_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_32_3 cert8_layer_8_32_3 23 cert8_layer_8_32_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 8 [])
      LColor.r LColor.b 23 cert8_seen_8_32_4 = cert8_component_8_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 8 []) LColor.r LColor.b
    cert8_seen_8_32_4 cert8_layer_8_32_4_eq 23

theorem cert8_step_8_32 :
    closedCollarIndexStepBool word fiber8 8 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_8_32)
    (by decide) (by decide)
    (by simpa [cert8_move_8_32] using cert8_component_8_32_eq)
    (by decide) (by decide) (by decide)

def cert8_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.b LColor.p cert8_seen_9_3_0 = cert8_layer_9_3_0 := by
  decide

def cert8_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_9_3_1 : List ChainEdge :=
  []

theorem cert8_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.b LColor.p cert8_seen_9_3_1 = cert8_layer_9_3_1 := by
  decide

theorem cert8_component_9_3_eq :
    closedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p 27 cert8_seen_9_3_0 = cert8_component_9_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.b LColor.p
    cert8_seen_9_3_0 cert8_layer_9_3_0 26 cert8_layer_9_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.b LColor.p 26 cert8_seen_9_3_1 = cert8_component_9_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 9 []) LColor.b LColor.p
    cert8_seen_9_3_1 cert8_layer_9_3_1_eq 26

theorem cert8_step_9_3 :
    closedCollarIndexStepBool word fiber8 9 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_9_3)
    (by decide) (by decide)
    (by simpa [cert8_move_9_3] using cert8_component_9_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_9_15 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_9_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_9_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_9_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_9_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.p cert8_seen_9_15_0 = cert8_layer_9_15_0 := by
  decide

def cert8_seen_9_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_9_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_9_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.p cert8_seen_9_15_1 = cert8_layer_9_15_1 := by
  decide

def cert8_seen_9_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_9_15_2 : List ChainEdge :=
  []

theorem cert8_layer_9_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.p cert8_seen_9_15_2 = cert8_layer_9_15_2 := by
  decide

theorem cert8_component_9_15_eq :
    closedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_9_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.p 27 cert8_seen_9_15_0 = cert8_component_9_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.p
    cert8_seen_9_15_0 cert8_layer_9_15_0 26 cert8_layer_9_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.p 26 cert8_seen_9_15_1 = cert8_component_9_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.p
    cert8_seen_9_15_1 cert8_layer_9_15_1 25 cert8_layer_9_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.p 25 cert8_seen_9_15_2 = cert8_component_9_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 9 []) LColor.r LColor.p
    cert8_seen_9_15_2 cert8_layer_9_15_2_eq 25

theorem cert8_step_9_15 :
    closedCollarIndexStepBool word fiber8 9 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_9_15)
    (by decide) (by decide)
    (by simpa [cert8_move_9_15] using cert8_component_9_15_eq)
    (by decide) (by decide) (by decide)

def cert8_move_9_33 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_9_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_9_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_33_0 = cert8_layer_9_33_0 := by
  decide

def cert8_seen_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_9_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_33_1 = cert8_layer_9_33_1 := by
  decide

def cert8_seen_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_9_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_33_2 = cert8_layer_9_33_2 := by
  decide

def cert8_seen_9_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_9_33_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_9_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_33_3 = cert8_layer_9_33_3 := by
  decide

def cert8_seen_9_33_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_9_33_4 : List ChainEdge :=
  []

theorem cert8_layer_9_33_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 9 [])
      LColor.r LColor.b cert8_seen_9_33_4 = cert8_layer_9_33_4 := by
  decide

theorem cert8_component_9_33_eq :
    closedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_9_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 27 cert8_seen_9_33_0 = cert8_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_33_0 cert8_layer_9_33_0 26 cert8_layer_9_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 26 cert8_seen_9_33_1 = cert8_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_33_1 cert8_layer_9_33_1 25 cert8_layer_9_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 25 cert8_seen_9_33_2 = cert8_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_33_2 cert8_layer_9_33_2 24 cert8_layer_9_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 24 cert8_seen_9_33_3 = cert8_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_33_3 cert8_layer_9_33_3 23 cert8_layer_9_33_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 9 [])
      LColor.r LColor.b 23 cert8_seen_9_33_4 = cert8_component_9_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 9 []) LColor.r LColor.b
    cert8_seen_9_33_4 cert8_layer_9_33_4_eq 23

theorem cert8_step_9_33 :
    closedCollarIndexStepBool word fiber8 9 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_9_33)
    (by decide) (by decide)
    (by simpa [cert8_move_9_33] using cert8_component_9_33_eq)
    (by decide) (by decide) (by decide)

def cert8_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.b LColor.p cert8_seen_10_4_0 = cert8_layer_10_4_0 := by
  decide

def cert8_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_10_4_1 : List ChainEdge :=
  []

theorem cert8_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.b LColor.p cert8_seen_10_4_1 = cert8_layer_10_4_1 := by
  decide

theorem cert8_component_10_4_eq :
    closedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p 27 cert8_seen_10_4_0 = cert8_component_10_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.b LColor.p
    cert8_seen_10_4_0 cert8_layer_10_4_0 26 cert8_layer_10_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.b LColor.p 26 cert8_seen_10_4_1 = cert8_component_10_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 10 []) LColor.b LColor.p
    cert8_seen_10_4_1 cert8_layer_10_4_1_eq 26

theorem cert8_step_10_4 :
    closedCollarIndexStepBool word fiber8 10 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_10_4)
    (by decide) (by decide)
    (by simpa [cert8_move_10_4] using cert8_component_10_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_10_16 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_10_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_10_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_10_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_10_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.p cert8_seen_10_16_0 = cert8_layer_10_16_0 := by
  decide

def cert8_seen_10_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_10_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_10_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.p cert8_seen_10_16_1 = cert8_layer_10_16_1 := by
  decide

def cert8_seen_10_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_10_16_2 : List ChainEdge :=
  []

theorem cert8_layer_10_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.p cert8_seen_10_16_2 = cert8_layer_10_16_2 := by
  decide

theorem cert8_component_10_16_eq :
    closedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_10_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.p 27 cert8_seen_10_16_0 = cert8_component_10_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.p
    cert8_seen_10_16_0 cert8_layer_10_16_0 26 cert8_layer_10_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.p 26 cert8_seen_10_16_1 = cert8_component_10_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.p
    cert8_seen_10_16_1 cert8_layer_10_16_1 25 cert8_layer_10_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.p 25 cert8_seen_10_16_2 = cert8_component_10_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 10 []) LColor.r LColor.p
    cert8_seen_10_16_2 cert8_layer_10_16_2_eq 25

theorem cert8_step_10_16 :
    closedCollarIndexStepBool word fiber8 10 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_10_16)
    (by decide) (by decide)
    (by simpa [cert8_move_10_16] using cert8_component_10_16_eq)
    (by decide) (by decide) (by decide)

def cert8_move_10_34 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_10_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_10_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_0 = cert8_layer_10_34_0 := by
  decide

def cert8_seen_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_10_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_1 = cert8_layer_10_34_1 := by
  decide

def cert8_seen_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_10_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_2 = cert8_layer_10_34_2 := by
  decide

def cert8_seen_10_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_10_34_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_10_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_3 = cert8_layer_10_34_3 := by
  decide

def cert8_seen_10_34_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_10_34_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_10_34_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_4 = cert8_layer_10_34_4 := by
  decide

def cert8_seen_10_34_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_10_34_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_10_34_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_5 = cert8_layer_10_34_5 := by
  decide

def cert8_seen_10_34_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_10_34_6 : List ChainEdge :=
  []

theorem cert8_layer_10_34_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 10 [])
      LColor.r LColor.b cert8_seen_10_34_6 = cert8_layer_10_34_6 := by
  decide

theorem cert8_component_10_34_eq :
    closedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_10_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 27 cert8_seen_10_34_0 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_0 cert8_layer_10_34_0 26 cert8_layer_10_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 26 cert8_seen_10_34_1 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_1 cert8_layer_10_34_1 25 cert8_layer_10_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 25 cert8_seen_10_34_2 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_2 cert8_layer_10_34_2 24 cert8_layer_10_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 24 cert8_seen_10_34_3 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_3 cert8_layer_10_34_3 23 cert8_layer_10_34_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 23 cert8_seen_10_34_4 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_4 cert8_layer_10_34_4 22 cert8_layer_10_34_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 22 cert8_seen_10_34_5 = cert8_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_5 cert8_layer_10_34_5 21 cert8_layer_10_34_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 10 [])
      LColor.r LColor.b 21 cert8_seen_10_34_6 = cert8_component_10_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 10 []) LColor.r LColor.b
    cert8_seen_10_34_6 cert8_layer_10_34_6_eq 21

theorem cert8_step_10_34 :
    closedCollarIndexStepBool word fiber8 10 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_10_34)
    (by decide) (by decide)
    (by simpa [cert8_move_10_34] using cert8_component_10_34_eq)
    (by decide) (by decide) (by decide)

def cert8_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert8_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert8_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert8_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.b LColor.p cert8_seen_11_5_0 = cert8_layer_11_5_0 := by
  decide

def cert8_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert8_layer_11_5_1 : List ChainEdge :=
  []

theorem cert8_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.b LColor.p cert8_seen_11_5_1 = cert8_layer_11_5_1 := by
  decide

theorem cert8_component_11_5_eq :
    closedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert8_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p 27 cert8_seen_11_5_0 = cert8_component_11_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.b LColor.p
    cert8_seen_11_5_0 cert8_layer_11_5_0 26 cert8_layer_11_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.b LColor.p 26 cert8_seen_11_5_1 = cert8_component_11_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 11 []) LColor.b LColor.p
    cert8_seen_11_5_1 cert8_layer_11_5_1_eq 26

theorem cert8_step_11_5 :
    closedCollarIndexStepBool word fiber8 11 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_11_5)
    (by decide) (by decide)
    (by simpa [cert8_move_11_5] using cert8_component_11_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_11_17 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_11_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_11_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_11_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_11_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.p cert8_seen_11_17_0 = cert8_layer_11_17_0 := by
  decide

def cert8_seen_11_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_11_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_11_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.p cert8_seen_11_17_1 = cert8_layer_11_17_1 := by
  decide

def cert8_seen_11_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_11_17_2 : List ChainEdge :=
  []

theorem cert8_layer_11_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.p cert8_seen_11_17_2 = cert8_layer_11_17_2 := by
  decide

theorem cert8_component_11_17_eq :
    closedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_11_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.p 27 cert8_seen_11_17_0 = cert8_component_11_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.p
    cert8_seen_11_17_0 cert8_layer_11_17_0 26 cert8_layer_11_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.p 26 cert8_seen_11_17_1 = cert8_component_11_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.p
    cert8_seen_11_17_1 cert8_layer_11_17_1 25 cert8_layer_11_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.p 25 cert8_seen_11_17_2 = cert8_component_11_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 11 []) LColor.r LColor.p
    cert8_seen_11_17_2 cert8_layer_11_17_2_eq 25

theorem cert8_step_11_17 :
    closedCollarIndexStepBool word fiber8 11 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_11_17)
    (by decide) (by decide)
    (by simpa [cert8_move_11_17] using cert8_component_11_17_eq)
    (by decide) (by decide) (by decide)

def cert8_move_11_35 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_11_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_11_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_0 = cert8_layer_11_35_0 := by
  decide

def cert8_seen_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_11_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_1 = cert8_layer_11_35_1 := by
  decide

def cert8_seen_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_11_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_2 = cert8_layer_11_35_2 := by
  decide

def cert8_seen_11_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_11_35_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_11_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_3 = cert8_layer_11_35_3 := by
  decide

def cert8_seen_11_35_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_11_35_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_11_35_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_4 = cert8_layer_11_35_4 := by
  decide

def cert8_seen_11_35_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_11_35_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_11_35_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_5 = cert8_layer_11_35_5 := by
  decide

def cert8_seen_11_35_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_11_35_6 : List ChainEdge :=
  []

theorem cert8_layer_11_35_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 11 [])
      LColor.r LColor.b cert8_seen_11_35_6 = cert8_layer_11_35_6 := by
  decide

theorem cert8_component_11_35_eq :
    closedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_11_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 27 cert8_seen_11_35_0 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_0 cert8_layer_11_35_0 26 cert8_layer_11_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 26 cert8_seen_11_35_1 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_1 cert8_layer_11_35_1 25 cert8_layer_11_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 25 cert8_seen_11_35_2 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_2 cert8_layer_11_35_2 24 cert8_layer_11_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 24 cert8_seen_11_35_3 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_3 cert8_layer_11_35_3 23 cert8_layer_11_35_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 23 cert8_seen_11_35_4 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_4 cert8_layer_11_35_4 22 cert8_layer_11_35_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 22 cert8_seen_11_35_5 = cert8_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_5 cert8_layer_11_35_5 21 cert8_layer_11_35_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 11 [])
      LColor.r LColor.b 21 cert8_seen_11_35_6 = cert8_component_11_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 11 []) LColor.r LColor.b
    cert8_seen_11_35_6 cert8_layer_11_35_6_eq 21

theorem cert8_step_11_35 :
    closedCollarIndexStepBool word fiber8 11 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_11_35)
    (by decide) (by decide)
    (by simpa [cert8_move_11_35] using cert8_component_11_35_eq)
    (by decide) (by decide) (by decide)

def cert8_move_12_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_12_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_12_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_12_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_12_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.p cert8_seen_12_6_0 = cert8_layer_12_6_0 := by
  decide

def cert8_seen_12_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_12_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_12_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.p cert8_seen_12_6_1 = cert8_layer_12_6_1 := by
  decide

def cert8_seen_12_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_12_6_2 : List ChainEdge :=
  []

theorem cert8_layer_12_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 12 [])
      LColor.r LColor.p cert8_seen_12_6_2 = cert8_layer_12_6_2 := by
  decide

theorem cert8_component_12_6_eq :
    closedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_12_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.p 27 cert8_seen_12_6_0 = cert8_component_12_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.r LColor.p
    cert8_seen_12_6_0 cert8_layer_12_6_0 26 cert8_layer_12_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.p 26 cert8_seen_12_6_1 = cert8_component_12_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 12 []) LColor.r LColor.p
    cert8_seen_12_6_1 cert8_layer_12_6_1 25 cert8_layer_12_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 12 [])
      LColor.r LColor.p 25 cert8_seen_12_6_2 = cert8_component_12_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 12 []) LColor.r LColor.p
    cert8_seen_12_6_2 cert8_layer_12_6_2_eq 25

theorem cert8_step_12_6 :
    closedCollarIndexStepBool word fiber8 12 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_12_6)
    (by decide) (by decide)
    (by simpa [cert8_move_12_6] using cert8_component_12_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_13_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_13_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_13_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_13_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_13_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.p cert8_seen_13_7_0 = cert8_layer_13_7_0 := by
  decide

def cert8_seen_13_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_13_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_13_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.p cert8_seen_13_7_1 = cert8_layer_13_7_1 := by
  decide

def cert8_seen_13_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_13_7_2 : List ChainEdge :=
  []

theorem cert8_layer_13_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 13 [])
      LColor.r LColor.p cert8_seen_13_7_2 = cert8_layer_13_7_2 := by
  decide

theorem cert8_component_13_7_eq :
    closedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_13_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.p 27 cert8_seen_13_7_0 = cert8_component_13_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.r LColor.p
    cert8_seen_13_7_0 cert8_layer_13_7_0 26 cert8_layer_13_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.p 26 cert8_seen_13_7_1 = cert8_component_13_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 13 []) LColor.r LColor.p
    cert8_seen_13_7_1 cert8_layer_13_7_1 25 cert8_layer_13_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 13 [])
      LColor.r LColor.p 25 cert8_seen_13_7_2 = cert8_component_13_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 13 []) LColor.r LColor.p
    cert8_seen_13_7_2 cert8_layer_13_7_2_eq 25

theorem cert8_step_13_7 :
    closedCollarIndexStepBool word fiber8 13 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_13_7)
    (by decide) (by decide)
    (by simpa [cert8_move_13_7] using cert8_component_13_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_14_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_14_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_14_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_14_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_14_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.p cert8_seen_14_8_0 = cert8_layer_14_8_0 := by
  decide

def cert8_seen_14_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_14_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_14_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.p cert8_seen_14_8_1 = cert8_layer_14_8_1 := by
  decide

def cert8_seen_14_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_14_8_2 : List ChainEdge :=
  []

theorem cert8_layer_14_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 14 [])
      LColor.r LColor.p cert8_seen_14_8_2 = cert8_layer_14_8_2 := by
  decide

theorem cert8_component_14_8_eq :
    closedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_14_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.p 27 cert8_seen_14_8_0 = cert8_component_14_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.r LColor.p
    cert8_seen_14_8_0 cert8_layer_14_8_0 26 cert8_layer_14_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.p 26 cert8_seen_14_8_1 = cert8_component_14_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 14 []) LColor.r LColor.p
    cert8_seen_14_8_1 cert8_layer_14_8_1 25 cert8_layer_14_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 14 [])
      LColor.r LColor.p 25 cert8_seen_14_8_2 = cert8_component_14_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 14 []) LColor.r LColor.p
    cert8_seen_14_8_2 cert8_layer_14_8_2_eq 25

theorem cert8_step_14_8 :
    closedCollarIndexStepBool word fiber8 14 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_14_8)
    (by decide) (by decide)
    (by simpa [cert8_move_14_8] using cert8_component_14_8_eq)
    (by decide) (by decide) (by decide)

def cert8_move_15_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_15_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_15_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_15_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_15_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.p cert8_seen_15_9_0 = cert8_layer_15_9_0 := by
  decide

def cert8_seen_15_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_15_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_15_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.p cert8_seen_15_9_1 = cert8_layer_15_9_1 := by
  decide

def cert8_seen_15_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_15_9_2 : List ChainEdge :=
  []

theorem cert8_layer_15_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 15 [])
      LColor.r LColor.p cert8_seen_15_9_2 = cert8_layer_15_9_2 := by
  decide

theorem cert8_component_15_9_eq :
    closedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_15_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.p 27 cert8_seen_15_9_0 = cert8_component_15_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.r LColor.p
    cert8_seen_15_9_0 cert8_layer_15_9_0 26 cert8_layer_15_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.p 26 cert8_seen_15_9_1 = cert8_component_15_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 15 []) LColor.r LColor.p
    cert8_seen_15_9_1 cert8_layer_15_9_1 25 cert8_layer_15_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 15 [])
      LColor.r LColor.p 25 cert8_seen_15_9_2 = cert8_component_15_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 15 []) LColor.r LColor.p
    cert8_seen_15_9_2 cert8_layer_15_9_2_eq 25

theorem cert8_step_15_9 :
    closedCollarIndexStepBool word fiber8 15 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_15_9)
    (by decide) (by decide)
    (by simpa [cert8_move_15_9] using cert8_component_15_9_eq)
    (by decide) (by decide) (by decide)

def cert8_move_16_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_16_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_16_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_16_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_16_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.p cert8_seen_16_10_0 = cert8_layer_16_10_0 := by
  decide

def cert8_seen_16_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_16_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_16_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.p cert8_seen_16_10_1 = cert8_layer_16_10_1 := by
  decide

def cert8_seen_16_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_16_10_2 : List ChainEdge :=
  []

theorem cert8_layer_16_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 16 [])
      LColor.r LColor.p cert8_seen_16_10_2 = cert8_layer_16_10_2 := by
  decide

theorem cert8_component_16_10_eq :
    closedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_16_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.p 27 cert8_seen_16_10_0 = cert8_component_16_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 16 []) LColor.r LColor.p
    cert8_seen_16_10_0 cert8_layer_16_10_0 26 cert8_layer_16_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.p 26 cert8_seen_16_10_1 = cert8_component_16_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 16 []) LColor.r LColor.p
    cert8_seen_16_10_1 cert8_layer_16_10_1 25 cert8_layer_16_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 16 [])
      LColor.r LColor.p 25 cert8_seen_16_10_2 = cert8_component_16_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 16 []) LColor.r LColor.p
    cert8_seen_16_10_2 cert8_layer_16_10_2_eq 25

theorem cert8_step_16_10 :
    closedCollarIndexStepBool word fiber8 16 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_16_10)
    (by decide) (by decide)
    (by simpa [cert8_move_16_10] using cert8_component_16_10_eq)
    (by decide) (by decide) (by decide)

def cert8_move_17_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_17_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_17_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_17_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_17_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.p cert8_seen_17_11_0 = cert8_layer_17_11_0 := by
  decide

def cert8_seen_17_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_17_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_17_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.p cert8_seen_17_11_1 = cert8_layer_17_11_1 := by
  decide

def cert8_seen_17_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_17_11_2 : List ChainEdge :=
  []

theorem cert8_layer_17_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 17 [])
      LColor.r LColor.p cert8_seen_17_11_2 = cert8_layer_17_11_2 := by
  decide

theorem cert8_component_17_11_eq :
    closedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_17_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.p 27 cert8_seen_17_11_0 = cert8_component_17_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 17 []) LColor.r LColor.p
    cert8_seen_17_11_0 cert8_layer_17_11_0 26 cert8_layer_17_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.p 26 cert8_seen_17_11_1 = cert8_component_17_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 17 []) LColor.r LColor.p
    cert8_seen_17_11_1 cert8_layer_17_11_1 25 cert8_layer_17_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 17 [])
      LColor.r LColor.p 25 cert8_seen_17_11_2 = cert8_component_17_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 17 []) LColor.r LColor.p
    cert8_seen_17_11_2 cert8_layer_17_11_2_eq 25

theorem cert8_step_17_11 :
    closedCollarIndexStepBool word fiber8 17 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_17_11)
    (by decide) (by decide)
    (by simpa [cert8_move_17_11] using cert8_component_17_11_eq)
    (by decide) (by decide) (by decide)

def cert8_move_18_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_18_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_18_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_18_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.p cert8_seen_18_0_0 = cert8_layer_18_0_0 := by
  decide

def cert8_seen_18_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_18_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_18_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.p cert8_seen_18_0_1 = cert8_layer_18_0_1 := by
  decide

def cert8_seen_18_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_18_0_2 : List ChainEdge :=
  []

theorem cert8_layer_18_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.p cert8_seen_18_0_2 = cert8_layer_18_0_2 := by
  decide

theorem cert8_component_18_0_eq :
    closedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_18_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.p 27 cert8_seen_18_0_0 = cert8_component_18_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.p
    cert8_seen_18_0_0 cert8_layer_18_0_0 26 cert8_layer_18_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.p 26 cert8_seen_18_0_1 = cert8_component_18_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.p
    cert8_seen_18_0_1 cert8_layer_18_0_1 25 cert8_layer_18_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.p 25 cert8_seen_18_0_2 = cert8_component_18_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 18 []) LColor.r LColor.p
    cert8_seen_18_0_2 cert8_layer_18_0_2_eq 25

theorem cert8_step_18_0 :
    closedCollarIndexStepBool word fiber8 18 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_18_0)
    (by decide) (by decide)
    (by simpa [cert8_move_18_0] using cert8_component_18_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_18_42 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_18_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_18_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_18_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_18_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_42_0 = cert8_layer_18_42_0 := by
  decide

def cert8_seen_18_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_18_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_18_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_42_1 = cert8_layer_18_42_1 := by
  decide

def cert8_seen_18_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_18_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_18_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_42_2 = cert8_layer_18_42_2 := by
  decide

def cert8_seen_18_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_18_42_3 : List ChainEdge :=
  []

theorem cert8_layer_18_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 18 [])
      LColor.r LColor.b cert8_seen_18_42_3 = cert8_layer_18_42_3 := by
  decide

theorem cert8_component_18_42_eq :
    closedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_18_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 27 cert8_seen_18_42_0 = cert8_component_18_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_42_0 cert8_layer_18_42_0 26 cert8_layer_18_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 26 cert8_seen_18_42_1 = cert8_component_18_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_42_1 cert8_layer_18_42_1 25 cert8_layer_18_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 25 cert8_seen_18_42_2 = cert8_component_18_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_42_2 cert8_layer_18_42_2 24 cert8_layer_18_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 18 [])
      LColor.r LColor.b 24 cert8_seen_18_42_3 = cert8_component_18_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 18 []) LColor.r LColor.b
    cert8_seen_18_42_3 cert8_layer_18_42_3_eq 24

theorem cert8_step_18_42 :
    closedCollarIndexStepBool word fiber8 18 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_18_42)
    (by decide) (by decide)
    (by simpa [cert8_move_18_42] using cert8_component_18_42_eq)
    (by decide) (by decide) (by decide)

def cert8_move_19_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_19_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_19_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_19_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.p cert8_seen_19_1_0 = cert8_layer_19_1_0 := by
  decide

def cert8_seen_19_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_19_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_19_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.p cert8_seen_19_1_1 = cert8_layer_19_1_1 := by
  decide

def cert8_seen_19_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_19_1_2 : List ChainEdge :=
  []

theorem cert8_layer_19_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.p cert8_seen_19_1_2 = cert8_layer_19_1_2 := by
  decide

theorem cert8_component_19_1_eq :
    closedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_19_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 19 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.p 27 cert8_seen_19_1_0 = cert8_component_19_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.p
    cert8_seen_19_1_0 cert8_layer_19_1_0 26 cert8_layer_19_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.p 26 cert8_seen_19_1_1 = cert8_component_19_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.p
    cert8_seen_19_1_1 cert8_layer_19_1_1 25 cert8_layer_19_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.p 25 cert8_seen_19_1_2 = cert8_component_19_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 19 []) LColor.r LColor.p
    cert8_seen_19_1_2 cert8_layer_19_1_2_eq 25

theorem cert8_step_19_1 :
    closedCollarIndexStepBool word fiber8 19 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_19_1)
    (by decide) (by decide)
    (by simpa [cert8_move_19_1] using cert8_component_19_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_19_43 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_19_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_19_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_19_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_19_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_43_0 = cert8_layer_19_43_0 := by
  decide

def cert8_seen_19_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_19_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_19_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_43_1 = cert8_layer_19_43_1 := by
  decide

def cert8_seen_19_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_19_43_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_19_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_43_2 = cert8_layer_19_43_2 := by
  decide

def cert8_seen_19_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_19_43_3 : List ChainEdge :=
  []

theorem cert8_layer_19_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 19 [])
      LColor.r LColor.b cert8_seen_19_43_3 = cert8_layer_19_43_3 := by
  decide

theorem cert8_component_19_43_eq :
    closedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_19_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 27 cert8_seen_19_43_0 = cert8_component_19_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_43_0 cert8_layer_19_43_0 26 cert8_layer_19_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 26 cert8_seen_19_43_1 = cert8_component_19_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_43_1 cert8_layer_19_43_1 25 cert8_layer_19_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 25 cert8_seen_19_43_2 = cert8_component_19_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_43_2 cert8_layer_19_43_2 24 cert8_layer_19_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 19 [])
      LColor.r LColor.b 24 cert8_seen_19_43_3 = cert8_component_19_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 19 []) LColor.r LColor.b
    cert8_seen_19_43_3 cert8_layer_19_43_3_eq 24

theorem cert8_step_19_43 :
    closedCollarIndexStepBool word fiber8 19 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_19_43)
    (by decide) (by decide)
    (by simpa [cert8_move_19_43] using cert8_component_19_43_eq)
    (by decide) (by decide) (by decide)

def cert8_move_20_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_20_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_20_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_20_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.p cert8_seen_20_2_0 = cert8_layer_20_2_0 := by
  decide

def cert8_seen_20_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_20_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_20_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.p cert8_seen_20_2_1 = cert8_layer_20_2_1 := by
  decide

def cert8_seen_20_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_20_2_2 : List ChainEdge :=
  []

theorem cert8_layer_20_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.p cert8_seen_20_2_2 = cert8_layer_20_2_2 := by
  decide

theorem cert8_component_20_2_eq :
    closedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_20_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 20 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.p 27 cert8_seen_20_2_0 = cert8_component_20_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.p
    cert8_seen_20_2_0 cert8_layer_20_2_0 26 cert8_layer_20_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.p 26 cert8_seen_20_2_1 = cert8_component_20_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.p
    cert8_seen_20_2_1 cert8_layer_20_2_1 25 cert8_layer_20_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.p 25 cert8_seen_20_2_2 = cert8_component_20_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 20 []) LColor.r LColor.p
    cert8_seen_20_2_2 cert8_layer_20_2_2_eq 25

theorem cert8_step_20_2 :
    closedCollarIndexStepBool word fiber8 20 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_20_2)
    (by decide) (by decide)
    (by simpa [cert8_move_20_2] using cert8_component_20_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_20_44 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_20_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_20_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_20_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_20_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_44_0 = cert8_layer_20_44_0 := by
  decide

def cert8_seen_20_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_20_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_20_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_44_1 = cert8_layer_20_44_1 := by
  decide

def cert8_seen_20_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_20_44_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_20_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_44_2 = cert8_layer_20_44_2 := by
  decide

def cert8_seen_20_44_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_20_44_3 : List ChainEdge :=
  []

theorem cert8_layer_20_44_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 20 [])
      LColor.r LColor.b cert8_seen_20_44_3 = cert8_layer_20_44_3 := by
  decide

theorem cert8_component_20_44_eq :
    closedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_20_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 27 cert8_seen_20_44_0 = cert8_component_20_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_44_0 cert8_layer_20_44_0 26 cert8_layer_20_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 26 cert8_seen_20_44_1 = cert8_component_20_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_44_1 cert8_layer_20_44_1 25 cert8_layer_20_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 25 cert8_seen_20_44_2 = cert8_component_20_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_44_2 cert8_layer_20_44_2 24 cert8_layer_20_44_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 20 [])
      LColor.r LColor.b 24 cert8_seen_20_44_3 = cert8_component_20_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 20 []) LColor.r LColor.b
    cert8_seen_20_44_3 cert8_layer_20_44_3_eq 24

theorem cert8_step_20_44 :
    closedCollarIndexStepBool word fiber8 20 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_20_44)
    (by decide) (by decide)
    (by simpa [cert8_move_20_44] using cert8_component_20_44_eq)
    (by decide) (by decide) (by decide)

def cert8_move_21_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_21_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_21_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_21_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.p cert8_seen_21_3_0 = cert8_layer_21_3_0 := by
  decide

def cert8_seen_21_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_21_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_21_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.p cert8_seen_21_3_1 = cert8_layer_21_3_1 := by
  decide

def cert8_seen_21_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_21_3_2 : List ChainEdge :=
  []

theorem cert8_layer_21_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.p cert8_seen_21_3_2 = cert8_layer_21_3_2 := by
  decide

theorem cert8_component_21_3_eq :
    closedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_21_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 21 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.p 27 cert8_seen_21_3_0 = cert8_component_21_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.p
    cert8_seen_21_3_0 cert8_layer_21_3_0 26 cert8_layer_21_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.p 26 cert8_seen_21_3_1 = cert8_component_21_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.p
    cert8_seen_21_3_1 cert8_layer_21_3_1 25 cert8_layer_21_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.p 25 cert8_seen_21_3_2 = cert8_component_21_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 21 []) LColor.r LColor.p
    cert8_seen_21_3_2 cert8_layer_21_3_2_eq 25

theorem cert8_step_21_3 :
    closedCollarIndexStepBool word fiber8 21 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_21_3)
    (by decide) (by decide)
    (by simpa [cert8_move_21_3] using cert8_component_21_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_21_45 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_21_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_21_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_21_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_21_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_45_0 = cert8_layer_21_45_0 := by
  decide

def cert8_seen_21_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_21_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_21_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_45_1 = cert8_layer_21_45_1 := by
  decide

def cert8_seen_21_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_21_45_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_21_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_45_2 = cert8_layer_21_45_2 := by
  decide

def cert8_seen_21_45_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_21_45_3 : List ChainEdge :=
  []

theorem cert8_layer_21_45_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 21 [])
      LColor.r LColor.b cert8_seen_21_45_3 = cert8_layer_21_45_3 := by
  decide

theorem cert8_component_21_45_eq :
    closedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_21_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 27 cert8_seen_21_45_0 = cert8_component_21_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_45_0 cert8_layer_21_45_0 26 cert8_layer_21_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 26 cert8_seen_21_45_1 = cert8_component_21_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_45_1 cert8_layer_21_45_1 25 cert8_layer_21_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 25 cert8_seen_21_45_2 = cert8_component_21_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_45_2 cert8_layer_21_45_2 24 cert8_layer_21_45_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 21 [])
      LColor.r LColor.b 24 cert8_seen_21_45_3 = cert8_component_21_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 21 []) LColor.r LColor.b
    cert8_seen_21_45_3 cert8_layer_21_45_3_eq 24

theorem cert8_step_21_45 :
    closedCollarIndexStepBool word fiber8 21 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_21_45)
    (by decide) (by decide)
    (by simpa [cert8_move_21_45] using cert8_component_21_45_eq)
    (by decide) (by decide) (by decide)

def cert8_move_22_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_22_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_22_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_22_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_22_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.p cert8_seen_22_4_0 = cert8_layer_22_4_0 := by
  decide

def cert8_seen_22_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_22_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_22_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.p cert8_seen_22_4_1 = cert8_layer_22_4_1 := by
  decide

def cert8_seen_22_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_22_4_2 : List ChainEdge :=
  []

theorem cert8_layer_22_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.p cert8_seen_22_4_2 = cert8_layer_22_4_2 := by
  decide

theorem cert8_component_22_4_eq :
    closedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_22_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 22 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.p 27 cert8_seen_22_4_0 = cert8_component_22_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.p
    cert8_seen_22_4_0 cert8_layer_22_4_0 26 cert8_layer_22_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.p 26 cert8_seen_22_4_1 = cert8_component_22_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.p
    cert8_seen_22_4_1 cert8_layer_22_4_1 25 cert8_layer_22_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.p 25 cert8_seen_22_4_2 = cert8_component_22_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 22 []) LColor.r LColor.p
    cert8_seen_22_4_2 cert8_layer_22_4_2_eq 25

theorem cert8_step_22_4 :
    closedCollarIndexStepBool word fiber8 22 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_22_4)
    (by decide) (by decide)
    (by simpa [cert8_move_22_4] using cert8_component_22_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_22_46 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_22_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_seen_22_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_22_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_22_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_0 = cert8_layer_22_46_0 := by
  decide

def cert8_seen_22_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_22_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_22_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_1 = cert8_layer_22_46_1 := by
  decide

def cert8_seen_22_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_22_46_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_22_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_2 = cert8_layer_22_46_2 := by
  decide

def cert8_seen_22_46_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_22_46_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_22_46_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_3 = cert8_layer_22_46_3 := by
  decide

def cert8_seen_22_46_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_22_46_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_22_46_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_4 = cert8_layer_22_46_4 := by
  decide

def cert8_seen_22_46_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_22_46_5 : List ChainEdge :=
  []

theorem cert8_layer_22_46_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 22 [])
      LColor.r LColor.b cert8_seen_22_46_5 = cert8_layer_22_46_5 := by
  decide

theorem cert8_component_22_46_eq :
    closedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_22_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 27 cert8_seen_22_46_0 = cert8_component_22_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_0 cert8_layer_22_46_0 26 cert8_layer_22_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 26 cert8_seen_22_46_1 = cert8_component_22_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_1 cert8_layer_22_46_1 25 cert8_layer_22_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 25 cert8_seen_22_46_2 = cert8_component_22_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_2 cert8_layer_22_46_2 24 cert8_layer_22_46_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 24 cert8_seen_22_46_3 = cert8_component_22_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_3 cert8_layer_22_46_3 23 cert8_layer_22_46_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 23 cert8_seen_22_46_4 = cert8_component_22_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_4 cert8_layer_22_46_4 22 cert8_layer_22_46_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 22 [])
      LColor.r LColor.b 22 cert8_seen_22_46_5 = cert8_component_22_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 22 []) LColor.r LColor.b
    cert8_seen_22_46_5 cert8_layer_22_46_5_eq 22

theorem cert8_step_22_46 :
    closedCollarIndexStepBool word fiber8 22 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_22_46)
    (by decide) (by decide)
    (by simpa [cert8_move_22_46] using cert8_component_22_46_eq)
    (by decide) (by decide) (by decide)

def cert8_move_23_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_23_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_23_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_23_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_23_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.p cert8_seen_23_5_0 = cert8_layer_23_5_0 := by
  decide

def cert8_seen_23_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_23_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_23_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.p cert8_seen_23_5_1 = cert8_layer_23_5_1 := by
  decide

def cert8_seen_23_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_23_5_2 : List ChainEdge :=
  []

theorem cert8_layer_23_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.p cert8_seen_23_5_2 = cert8_layer_23_5_2 := by
  decide

theorem cert8_component_23_5_eq :
    closedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_23_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 23 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.p 27 cert8_seen_23_5_0 = cert8_component_23_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.p
    cert8_seen_23_5_0 cert8_layer_23_5_0 26 cert8_layer_23_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.p 26 cert8_seen_23_5_1 = cert8_component_23_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.p
    cert8_seen_23_5_1 cert8_layer_23_5_1 25 cert8_layer_23_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.p 25 cert8_seen_23_5_2 = cert8_component_23_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 23 []) LColor.r LColor.p
    cert8_seen_23_5_2 cert8_layer_23_5_2_eq 25

theorem cert8_step_23_5 :
    closedCollarIndexStepBool word fiber8 23 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_23_5)
    (by decide) (by decide)
    (by simpa [cert8_move_23_5] using cert8_component_23_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_23_47 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_23_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_seen_23_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_23_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_23_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_0 = cert8_layer_23_47_0 := by
  decide

def cert8_seen_23_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_23_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_23_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_1 = cert8_layer_23_47_1 := by
  decide

def cert8_seen_23_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_23_47_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_23_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_2 = cert8_layer_23_47_2 := by
  decide

def cert8_seen_23_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_23_47_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_23_47_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_3 = cert8_layer_23_47_3 := by
  decide

def cert8_seen_23_47_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_23_47_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_23_47_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_4 = cert8_layer_23_47_4 := by
  decide

def cert8_seen_23_47_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_23_47_5 : List ChainEdge :=
  []

theorem cert8_layer_23_47_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 23 [])
      LColor.r LColor.b cert8_seen_23_47_5 = cert8_layer_23_47_5 := by
  decide

theorem cert8_component_23_47_eq :
    closedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_23_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 27 cert8_seen_23_47_0 = cert8_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_0 cert8_layer_23_47_0 26 cert8_layer_23_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 26 cert8_seen_23_47_1 = cert8_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_1 cert8_layer_23_47_1 25 cert8_layer_23_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 25 cert8_seen_23_47_2 = cert8_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_2 cert8_layer_23_47_2 24 cert8_layer_23_47_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 24 cert8_seen_23_47_3 = cert8_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_3 cert8_layer_23_47_3 23 cert8_layer_23_47_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 23 cert8_seen_23_47_4 = cert8_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_4 cert8_layer_23_47_4 22 cert8_layer_23_47_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 23 [])
      LColor.r LColor.b 22 cert8_seen_23_47_5 = cert8_component_23_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 23 []) LColor.r LColor.b
    cert8_seen_23_47_5 cert8_layer_23_47_5_eq 22

theorem cert8_step_23_47 :
    closedCollarIndexStepBool word fiber8 23 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_23_47)
    (by decide) (by decide)
    (by simpa [cert8_move_23_47] using cert8_component_23_47_eq)
    (by decide) (by decide) (by decide)

def cert8_move_24_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_24_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_0_0 = cert8_layer_24_0_0 := by
  decide

def cert8_seen_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_24_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_0_1 = cert8_layer_24_0_1 := by
  decide

def cert8_seen_24_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_24_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_24_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_0_2 = cert8_layer_24_0_2 := by
  decide

def cert8_seen_24_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_24_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_24_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_0_3 = cert8_layer_24_0_3 := by
  decide

def cert8_seen_24_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_24_0_4 : List ChainEdge :=
  []

theorem cert8_layer_24_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.r LColor.b cert8_seen_24_0_4 = cert8_layer_24_0_4 := by
  decide

theorem cert8_component_24_0_eq :
    closedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_24_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 27 cert8_seen_24_0_0 = cert8_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_0_0 cert8_layer_24_0_0 26 cert8_layer_24_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 26 cert8_seen_24_0_1 = cert8_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_0_1 cert8_layer_24_0_1 25 cert8_layer_24_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 25 cert8_seen_24_0_2 = cert8_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_0_2 cert8_layer_24_0_2 24 cert8_layer_24_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 24 cert8_seen_24_0_3 = cert8_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_0_3 cert8_layer_24_0_3 23 cert8_layer_24_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.r LColor.b 23 cert8_seen_24_0_4 = cert8_component_24_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 24 []) LColor.r LColor.b
    cert8_seen_24_0_4 cert8_layer_24_0_4_eq 23

theorem cert8_step_24_0 :
    closedCollarIndexStepBool word fiber8 24 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_24_0)
    (by decide) (by decide)
    (by simpa [cert8_move_24_0] using cert8_component_24_0_eq)
    (by decide) (by decide) (by decide)

def cert8_move_24_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_24_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_24_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_24_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_24_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.b LColor.p cert8_seen_24_36_0 = cert8_layer_24_36_0 := by
  decide

def cert8_seen_24_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_24_36_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_24_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.b LColor.p cert8_seen_24_36_1 = cert8_layer_24_36_1 := by
  decide

def cert8_seen_24_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_24_36_2 : List ChainEdge :=
  []

theorem cert8_layer_24_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 24 [])
      LColor.b LColor.p cert8_seen_24_36_2 = cert8_layer_24_36_2 := by
  decide

theorem cert8_component_24_36_eq :
    closedCollarComponent word (listGetD fiber8 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_24_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.b LColor.p 27 cert8_seen_24_36_0 = cert8_component_24_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.b LColor.p
    cert8_seen_24_36_0 cert8_layer_24_36_0 26 cert8_layer_24_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.b LColor.p 26 cert8_seen_24_36_1 = cert8_component_24_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 24 []) LColor.b LColor.p
    cert8_seen_24_36_1 cert8_layer_24_36_1 25 cert8_layer_24_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 24 [])
      LColor.b LColor.p 25 cert8_seen_24_36_2 = cert8_component_24_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 24 []) LColor.b LColor.p
    cert8_seen_24_36_2 cert8_layer_24_36_2_eq 25

theorem cert8_step_24_36 :
    closedCollarIndexStepBool word fiber8 24 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_24_36)
    (by decide) (by decide)
    (by simpa [cert8_move_24_36] using cert8_component_24_36_eq)
    (by decide) (by decide) (by decide)

def cert8_move_25_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_25_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_1_0 = cert8_layer_25_1_0 := by
  decide

def cert8_seen_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_25_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_1_1 = cert8_layer_25_1_1 := by
  decide

def cert8_seen_25_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_25_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_25_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_1_2 = cert8_layer_25_1_2 := by
  decide

def cert8_seen_25_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_25_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_25_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_1_3 = cert8_layer_25_1_3 := by
  decide

def cert8_seen_25_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_25_1_4 : List ChainEdge :=
  []

theorem cert8_layer_25_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.r LColor.b cert8_seen_25_1_4 = cert8_layer_25_1_4 := by
  decide

theorem cert8_component_25_1_eq :
    closedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_25_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 27 cert8_seen_25_1_0 = cert8_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_1_0 cert8_layer_25_1_0 26 cert8_layer_25_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 26 cert8_seen_25_1_1 = cert8_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_1_1 cert8_layer_25_1_1 25 cert8_layer_25_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 25 cert8_seen_25_1_2 = cert8_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_1_2 cert8_layer_25_1_2 24 cert8_layer_25_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 24 cert8_seen_25_1_3 = cert8_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_1_3 cert8_layer_25_1_3 23 cert8_layer_25_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.r LColor.b 23 cert8_seen_25_1_4 = cert8_component_25_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 25 []) LColor.r LColor.b
    cert8_seen_25_1_4 cert8_layer_25_1_4_eq 23

theorem cert8_step_25_1 :
    closedCollarIndexStepBool word fiber8 25 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_25_1)
    (by decide) (by decide)
    (by simpa [cert8_move_25_1] using cert8_component_25_1_eq)
    (by decide) (by decide) (by decide)

def cert8_move_25_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_25_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_25_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_25_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_25_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.b LColor.p cert8_seen_25_37_0 = cert8_layer_25_37_0 := by
  decide

def cert8_seen_25_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_25_37_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_25_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.b LColor.p cert8_seen_25_37_1 = cert8_layer_25_37_1 := by
  decide

def cert8_seen_25_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_25_37_2 : List ChainEdge :=
  []

theorem cert8_layer_25_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 25 [])
      LColor.b LColor.p cert8_seen_25_37_2 = cert8_layer_25_37_2 := by
  decide

theorem cert8_component_25_37_eq :
    closedCollarComponent word (listGetD fiber8 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_25_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.b LColor.p 27 cert8_seen_25_37_0 = cert8_component_25_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.b LColor.p
    cert8_seen_25_37_0 cert8_layer_25_37_0 26 cert8_layer_25_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.b LColor.p 26 cert8_seen_25_37_1 = cert8_component_25_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 25 []) LColor.b LColor.p
    cert8_seen_25_37_1 cert8_layer_25_37_1 25 cert8_layer_25_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 25 [])
      LColor.b LColor.p 25 cert8_seen_25_37_2 = cert8_component_25_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 25 []) LColor.b LColor.p
    cert8_seen_25_37_2 cert8_layer_25_37_2_eq 25

theorem cert8_step_25_37 :
    closedCollarIndexStepBool word fiber8 25 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_25_37)
    (by decide) (by decide)
    (by simpa [cert8_move_25_37] using cert8_component_25_37_eq)
    (by decide) (by decide) (by decide)

def cert8_move_26_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_26_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_2_0 = cert8_layer_26_2_0 := by
  decide

def cert8_seen_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_26_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_2_1 = cert8_layer_26_2_1 := by
  decide

def cert8_seen_26_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_26_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_26_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_2_2 = cert8_layer_26_2_2 := by
  decide

def cert8_seen_26_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_26_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_26_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_2_3 = cert8_layer_26_2_3 := by
  decide

def cert8_seen_26_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_26_2_4 : List ChainEdge :=
  []

theorem cert8_layer_26_2_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.r LColor.b cert8_seen_26_2_4 = cert8_layer_26_2_4 := by
  decide

theorem cert8_component_26_2_eq :
    closedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_26_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 27 cert8_seen_26_2_0 = cert8_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_2_0 cert8_layer_26_2_0 26 cert8_layer_26_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 26 cert8_seen_26_2_1 = cert8_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_2_1 cert8_layer_26_2_1 25 cert8_layer_26_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 25 cert8_seen_26_2_2 = cert8_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_2_2 cert8_layer_26_2_2 24 cert8_layer_26_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 24 cert8_seen_26_2_3 = cert8_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_2_3 cert8_layer_26_2_3 23 cert8_layer_26_2_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.r LColor.b 23 cert8_seen_26_2_4 = cert8_component_26_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 26 []) LColor.r LColor.b
    cert8_seen_26_2_4 cert8_layer_26_2_4_eq 23

theorem cert8_step_26_2 :
    closedCollarIndexStepBool word fiber8 26 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_26_2)
    (by decide) (by decide)
    (by simpa [cert8_move_26_2] using cert8_component_26_2_eq)
    (by decide) (by decide) (by decide)

def cert8_move_26_38 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_26_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_26_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_26_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_26_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.b LColor.p cert8_seen_26_38_0 = cert8_layer_26_38_0 := by
  decide

def cert8_seen_26_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_26_38_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_26_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.b LColor.p cert8_seen_26_38_1 = cert8_layer_26_38_1 := by
  decide

def cert8_seen_26_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_26_38_2 : List ChainEdge :=
  []

theorem cert8_layer_26_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 26 [])
      LColor.b LColor.p cert8_seen_26_38_2 = cert8_layer_26_38_2 := by
  decide

theorem cert8_component_26_38_eq :
    closedCollarComponent word (listGetD fiber8 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_26_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.b LColor.p 27 cert8_seen_26_38_0 = cert8_component_26_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.b LColor.p
    cert8_seen_26_38_0 cert8_layer_26_38_0 26 cert8_layer_26_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.b LColor.p 26 cert8_seen_26_38_1 = cert8_component_26_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 26 []) LColor.b LColor.p
    cert8_seen_26_38_1 cert8_layer_26_38_1 25 cert8_layer_26_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 26 [])
      LColor.b LColor.p 25 cert8_seen_26_38_2 = cert8_component_26_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 26 []) LColor.b LColor.p
    cert8_seen_26_38_2 cert8_layer_26_38_2_eq 25

theorem cert8_step_26_38 :
    closedCollarIndexStepBool word fiber8 26 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_26_38)
    (by decide) (by decide)
    (by simpa [cert8_move_26_38] using cert8_component_26_38_eq)
    (by decide) (by decide) (by decide)

def cert8_move_27_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_27_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_3_0 = cert8_layer_27_3_0 := by
  decide

def cert8_seen_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_27_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_3_1 = cert8_layer_27_3_1 := by
  decide

def cert8_seen_27_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_27_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_27_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_3_2 = cert8_layer_27_3_2 := by
  decide

def cert8_seen_27_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_27_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_27_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_3_3 = cert8_layer_27_3_3 := by
  decide

def cert8_seen_27_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_27_3_4 : List ChainEdge :=
  []

theorem cert8_layer_27_3_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.r LColor.b cert8_seen_27_3_4 = cert8_layer_27_3_4 := by
  decide

theorem cert8_component_27_3_eq :
    closedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_27_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 27 cert8_seen_27_3_0 = cert8_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_3_0 cert8_layer_27_3_0 26 cert8_layer_27_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 26 cert8_seen_27_3_1 = cert8_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_3_1 cert8_layer_27_3_1 25 cert8_layer_27_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 25 cert8_seen_27_3_2 = cert8_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_3_2 cert8_layer_27_3_2 24 cert8_layer_27_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 24 cert8_seen_27_3_3 = cert8_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_3_3 cert8_layer_27_3_3 23 cert8_layer_27_3_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.r LColor.b 23 cert8_seen_27_3_4 = cert8_component_27_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 27 []) LColor.r LColor.b
    cert8_seen_27_3_4 cert8_layer_27_3_4_eq 23

theorem cert8_step_27_3 :
    closedCollarIndexStepBool word fiber8 27 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_27_3)
    (by decide) (by decide)
    (by simpa [cert8_move_27_3] using cert8_component_27_3_eq)
    (by decide) (by decide) (by decide)

def cert8_move_27_39 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_27_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_27_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_27_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_27_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.b LColor.p cert8_seen_27_39_0 = cert8_layer_27_39_0 := by
  decide

def cert8_seen_27_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_27_39_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_27_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.b LColor.p cert8_seen_27_39_1 = cert8_layer_27_39_1 := by
  decide

def cert8_seen_27_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_27_39_2 : List ChainEdge :=
  []

theorem cert8_layer_27_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 27 [])
      LColor.b LColor.p cert8_seen_27_39_2 = cert8_layer_27_39_2 := by
  decide

theorem cert8_component_27_39_eq :
    closedCollarComponent word (listGetD fiber8 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_27_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.b LColor.p 27 cert8_seen_27_39_0 = cert8_component_27_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.b LColor.p
    cert8_seen_27_39_0 cert8_layer_27_39_0 26 cert8_layer_27_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.b LColor.p 26 cert8_seen_27_39_1 = cert8_component_27_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 27 []) LColor.b LColor.p
    cert8_seen_27_39_1 cert8_layer_27_39_1 25 cert8_layer_27_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 27 [])
      LColor.b LColor.p 25 cert8_seen_27_39_2 = cert8_component_27_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 27 []) LColor.b LColor.p
    cert8_seen_27_39_2 cert8_layer_27_39_2_eq 25

theorem cert8_step_27_39 :
    closedCollarIndexStepBool word fiber8 27 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_27_39)
    (by decide) (by decide)
    (by simpa [cert8_move_27_39] using cert8_component_27_39_eq)
    (by decide) (by decide) (by decide)

def cert8_move_28_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_28_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_28_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_28_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_28_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_0 = cert8_layer_28_4_0 := by
  decide

def cert8_seen_28_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_28_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_28_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_1 = cert8_layer_28_4_1 := by
  decide

def cert8_seen_28_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_28_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_28_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_2 = cert8_layer_28_4_2 := by
  decide

def cert8_seen_28_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_28_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_28_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_3 = cert8_layer_28_4_3 := by
  decide

def cert8_seen_28_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_28_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_28_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_4 = cert8_layer_28_4_4 := by
  decide

def cert8_seen_28_4_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_28_4_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_28_4_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_5 = cert8_layer_28_4_5 := by
  decide

def cert8_seen_28_4_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_28_4_6 : List ChainEdge :=
  []

theorem cert8_layer_28_4_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.r LColor.b cert8_seen_28_4_6 = cert8_layer_28_4_6 := by
  decide

theorem cert8_component_28_4_eq :
    closedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_28_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 27 cert8_seen_28_4_0 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_0 cert8_layer_28_4_0 26 cert8_layer_28_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 26 cert8_seen_28_4_1 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_1 cert8_layer_28_4_1 25 cert8_layer_28_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 25 cert8_seen_28_4_2 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_2 cert8_layer_28_4_2 24 cert8_layer_28_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 24 cert8_seen_28_4_3 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_3 cert8_layer_28_4_3 23 cert8_layer_28_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 23 cert8_seen_28_4_4 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_4 cert8_layer_28_4_4 22 cert8_layer_28_4_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 22 cert8_seen_28_4_5 = cert8_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_5 cert8_layer_28_4_5 21 cert8_layer_28_4_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.r LColor.b 21 cert8_seen_28_4_6 = cert8_component_28_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 28 []) LColor.r LColor.b
    cert8_seen_28_4_6 cert8_layer_28_4_6_eq 21

theorem cert8_step_28_4 :
    closedCollarIndexStepBool word fiber8 28 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_28_4)
    (by decide) (by decide)
    (by simpa [cert8_move_28_4] using cert8_component_28_4_eq)
    (by decide) (by decide) (by decide)

def cert8_move_28_40 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_28_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_28_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_28_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_28_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.b LColor.p cert8_seen_28_40_0 = cert8_layer_28_40_0 := by
  decide

def cert8_seen_28_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_28_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_28_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.b LColor.p cert8_seen_28_40_1 = cert8_layer_28_40_1 := by
  decide

def cert8_seen_28_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_28_40_2 : List ChainEdge :=
  []

theorem cert8_layer_28_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 28 [])
      LColor.b LColor.p cert8_seen_28_40_2 = cert8_layer_28_40_2 := by
  decide

theorem cert8_component_28_40_eq :
    closedCollarComponent word (listGetD fiber8 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_28_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.b LColor.p 27 cert8_seen_28_40_0 = cert8_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.b LColor.p
    cert8_seen_28_40_0 cert8_layer_28_40_0 26 cert8_layer_28_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.b LColor.p 26 cert8_seen_28_40_1 = cert8_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 28 []) LColor.b LColor.p
    cert8_seen_28_40_1 cert8_layer_28_40_1 25 cert8_layer_28_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 28 [])
      LColor.b LColor.p 25 cert8_seen_28_40_2 = cert8_component_28_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 28 []) LColor.b LColor.p
    cert8_seen_28_40_2 cert8_layer_28_40_2_eq 25

theorem cert8_step_28_40 :
    closedCollarIndexStepBool word fiber8 28 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_28_40)
    (by decide) (by decide)
    (by simpa [cert8_move_28_40] using cert8_component_28_40_eq)
    (by decide) (by decide) (by decide)

def cert8_move_29_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_29_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_29_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_29_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_29_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_0 = cert8_layer_29_5_0 := by
  decide

def cert8_seen_29_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_29_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_29_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_1 = cert8_layer_29_5_1 := by
  decide

def cert8_seen_29_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_29_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_29_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_2 = cert8_layer_29_5_2 := by
  decide

def cert8_seen_29_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_29_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_29_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_3 = cert8_layer_29_5_3 := by
  decide

def cert8_seen_29_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_29_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_29_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_4 = cert8_layer_29_5_4 := by
  decide

def cert8_seen_29_5_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_29_5_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_29_5_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_5 = cert8_layer_29_5_5 := by
  decide

def cert8_seen_29_5_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_29_5_6 : List ChainEdge :=
  []

theorem cert8_layer_29_5_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.r LColor.b cert8_seen_29_5_6 = cert8_layer_29_5_6 := by
  decide

theorem cert8_component_29_5_eq :
    closedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_29_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 27 cert8_seen_29_5_0 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_0 cert8_layer_29_5_0 26 cert8_layer_29_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 26 cert8_seen_29_5_1 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_1 cert8_layer_29_5_1 25 cert8_layer_29_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 25 cert8_seen_29_5_2 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_2 cert8_layer_29_5_2 24 cert8_layer_29_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 24 cert8_seen_29_5_3 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_3 cert8_layer_29_5_3 23 cert8_layer_29_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 23 cert8_seen_29_5_4 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_4 cert8_layer_29_5_4 22 cert8_layer_29_5_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 22 cert8_seen_29_5_5 = cert8_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_5 cert8_layer_29_5_5 21 cert8_layer_29_5_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.r LColor.b 21 cert8_seen_29_5_6 = cert8_component_29_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 29 []) LColor.r LColor.b
    cert8_seen_29_5_6 cert8_layer_29_5_6_eq 21

theorem cert8_step_29_5 :
    closedCollarIndexStepBool word fiber8 29 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_29_5)
    (by decide) (by decide)
    (by simpa [cert8_move_29_5] using cert8_component_29_5_eq)
    (by decide) (by decide) (by decide)

def cert8_move_29_41 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_29_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_29_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_29_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_29_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.b LColor.p cert8_seen_29_41_0 = cert8_layer_29_41_0 := by
  decide

def cert8_seen_29_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_29_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_29_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.b LColor.p cert8_seen_29_41_1 = cert8_layer_29_41_1 := by
  decide

def cert8_seen_29_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_29_41_2 : List ChainEdge :=
  []

theorem cert8_layer_29_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 29 [])
      LColor.b LColor.p cert8_seen_29_41_2 = cert8_layer_29_41_2 := by
  decide

theorem cert8_component_29_41_eq :
    closedCollarComponent word (listGetD fiber8 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_29_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.b LColor.p 27 cert8_seen_29_41_0 = cert8_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.b LColor.p
    cert8_seen_29_41_0 cert8_layer_29_41_0 26 cert8_layer_29_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.b LColor.p 26 cert8_seen_29_41_1 = cert8_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 29 []) LColor.b LColor.p
    cert8_seen_29_41_1 cert8_layer_29_41_1 25 cert8_layer_29_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 29 [])
      LColor.b LColor.p 25 cert8_seen_29_41_2 = cert8_component_29_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 29 []) LColor.b LColor.p
    cert8_seen_29_41_2 cert8_layer_29_41_2_eq 25

theorem cert8_step_29_41 :
    closedCollarIndexStepBool word fiber8 29 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_29_41)
    (by decide) (by decide)
    (by simpa [cert8_move_29_41] using cert8_component_29_41_eq)
    (by decide) (by decide) (by decide)

def cert8_move_30_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_30_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_30_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_6_0 = cert8_layer_30_6_0 := by
  decide

def cert8_seen_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_30_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_6_1 = cert8_layer_30_6_1 := by
  decide

def cert8_seen_30_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_30_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_30_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_6_2 = cert8_layer_30_6_2 := by
  decide

def cert8_seen_30_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_30_6_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_30_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_6_3 = cert8_layer_30_6_3 := by
  decide

def cert8_seen_30_6_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_30_6_4 : List ChainEdge :=
  []

theorem cert8_layer_30_6_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 30 [])
      LColor.r LColor.b cert8_seen_30_6_4 = cert8_layer_30_6_4 := by
  decide

theorem cert8_component_30_6_eq :
    closedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_30_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 27 cert8_seen_30_6_0 = cert8_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_6_0 cert8_layer_30_6_0 26 cert8_layer_30_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 26 cert8_seen_30_6_1 = cert8_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_6_1 cert8_layer_30_6_1 25 cert8_layer_30_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 25 cert8_seen_30_6_2 = cert8_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_6_2 cert8_layer_30_6_2 24 cert8_layer_30_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 24 cert8_seen_30_6_3 = cert8_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_6_3 cert8_layer_30_6_3 23 cert8_layer_30_6_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 30 [])
      LColor.r LColor.b 23 cert8_seen_30_6_4 = cert8_component_30_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 30 []) LColor.r LColor.b
    cert8_seen_30_6_4 cert8_layer_30_6_4_eq 23

theorem cert8_step_30_6 :
    closedCollarIndexStepBool word fiber8 30 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_30_6)
    (by decide) (by decide)
    (by simpa [cert8_move_30_6] using cert8_component_30_6_eq)
    (by decide) (by decide) (by decide)

def cert8_move_31_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_31_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_31_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_7_0 = cert8_layer_31_7_0 := by
  decide

def cert8_seen_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_31_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_7_1 = cert8_layer_31_7_1 := by
  decide

def cert8_seen_31_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_31_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_31_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_7_2 = cert8_layer_31_7_2 := by
  decide

def cert8_seen_31_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_31_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_31_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_7_3 = cert8_layer_31_7_3 := by
  decide

def cert8_seen_31_7_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_31_7_4 : List ChainEdge :=
  []

theorem cert8_layer_31_7_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 31 [])
      LColor.r LColor.b cert8_seen_31_7_4 = cert8_layer_31_7_4 := by
  decide

theorem cert8_component_31_7_eq :
    closedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_31_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 27 cert8_seen_31_7_0 = cert8_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_7_0 cert8_layer_31_7_0 26 cert8_layer_31_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 26 cert8_seen_31_7_1 = cert8_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_7_1 cert8_layer_31_7_1 25 cert8_layer_31_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 25 cert8_seen_31_7_2 = cert8_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_7_2 cert8_layer_31_7_2 24 cert8_layer_31_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 24 cert8_seen_31_7_3 = cert8_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_7_3 cert8_layer_31_7_3 23 cert8_layer_31_7_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 31 [])
      LColor.r LColor.b 23 cert8_seen_31_7_4 = cert8_component_31_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 31 []) LColor.r LColor.b
    cert8_seen_31_7_4 cert8_layer_31_7_4_eq 23

theorem cert8_step_31_7 :
    closedCollarIndexStepBool word fiber8 31 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_31_7)
    (by decide) (by decide)
    (by simpa [cert8_move_31_7] using cert8_component_31_7_eq)
    (by decide) (by decide) (by decide)

def cert8_move_32_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_32_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_32_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.b cert8_seen_32_8_0 = cert8_layer_32_8_0 := by
  decide

def cert8_seen_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_32_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.b cert8_seen_32_8_1 = cert8_layer_32_8_1 := by
  decide

def cert8_seen_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_32_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.b cert8_seen_32_8_2 = cert8_layer_32_8_2 := by
  decide

def cert8_seen_32_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_32_8_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_32_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.b cert8_seen_32_8_3 = cert8_layer_32_8_3 := by
  decide

def cert8_seen_32_8_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_32_8_4 : List ChainEdge :=
  []

theorem cert8_layer_32_8_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 32 [])
      LColor.r LColor.b cert8_seen_32_8_4 = cert8_layer_32_8_4 := by
  decide

theorem cert8_component_32_8_eq :
    closedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_32_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 32 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b 27 cert8_seen_32_8_0 = cert8_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.b
    cert8_seen_32_8_0 cert8_layer_32_8_0 26 cert8_layer_32_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b 26 cert8_seen_32_8_1 = cert8_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.b
    cert8_seen_32_8_1 cert8_layer_32_8_1 25 cert8_layer_32_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b 25 cert8_seen_32_8_2 = cert8_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.b
    cert8_seen_32_8_2 cert8_layer_32_8_2 24 cert8_layer_32_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b 24 cert8_seen_32_8_3 = cert8_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 32 []) LColor.r LColor.b
    cert8_seen_32_8_3 cert8_layer_32_8_3 23 cert8_layer_32_8_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 32 [])
      LColor.r LColor.b 23 cert8_seen_32_8_4 = cert8_component_32_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 32 []) LColor.r LColor.b
    cert8_seen_32_8_4 cert8_layer_32_8_4_eq 23

theorem cert8_step_32_8 :
    closedCollarIndexStepBool word fiber8 32 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_32_8)
    (by decide) (by decide)
    (by simpa [cert8_move_32_8] using cert8_component_32_8_eq)
    (by decide) (by decide) (by decide)

def cert8_move_33_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_33_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_33_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.b cert8_seen_33_9_0 = cert8_layer_33_9_0 := by
  decide

def cert8_seen_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_33_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.b cert8_seen_33_9_1 = cert8_layer_33_9_1 := by
  decide

def cert8_seen_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_33_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.b cert8_seen_33_9_2 = cert8_layer_33_9_2 := by
  decide

def cert8_seen_33_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_33_9_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_33_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.b cert8_seen_33_9_3 = cert8_layer_33_9_3 := by
  decide

def cert8_seen_33_9_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_33_9_4 : List ChainEdge :=
  []

theorem cert8_layer_33_9_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 33 [])
      LColor.r LColor.b cert8_seen_33_9_4 = cert8_layer_33_9_4 := by
  decide

theorem cert8_component_33_9_eq :
    closedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_33_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 33 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b 27 cert8_seen_33_9_0 = cert8_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.b
    cert8_seen_33_9_0 cert8_layer_33_9_0 26 cert8_layer_33_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b 26 cert8_seen_33_9_1 = cert8_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.b
    cert8_seen_33_9_1 cert8_layer_33_9_1 25 cert8_layer_33_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b 25 cert8_seen_33_9_2 = cert8_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.b
    cert8_seen_33_9_2 cert8_layer_33_9_2 24 cert8_layer_33_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b 24 cert8_seen_33_9_3 = cert8_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 33 []) LColor.r LColor.b
    cert8_seen_33_9_3 cert8_layer_33_9_3 23 cert8_layer_33_9_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 33 [])
      LColor.r LColor.b 23 cert8_seen_33_9_4 = cert8_component_33_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 33 []) LColor.r LColor.b
    cert8_seen_33_9_4 cert8_layer_33_9_4_eq 23

theorem cert8_step_33_9 :
    closedCollarIndexStepBool word fiber8 33 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_33_9)
    (by decide) (by decide)
    (by simpa [cert8_move_33_9] using cert8_component_33_9_eq)
    (by decide) (by decide) (by decide)

def cert8_move_34_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_34_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_34_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_0 = cert8_layer_34_10_0 := by
  decide

def cert8_seen_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_34_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_1 = cert8_layer_34_10_1 := by
  decide

def cert8_seen_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_34_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_2 = cert8_layer_34_10_2 := by
  decide

def cert8_seen_34_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_34_10_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_34_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_3 = cert8_layer_34_10_3 := by
  decide

def cert8_seen_34_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_34_10_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_34_10_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_4 = cert8_layer_34_10_4 := by
  decide

def cert8_seen_34_10_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_34_10_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_34_10_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_5 = cert8_layer_34_10_5 := by
  decide

def cert8_seen_34_10_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_34_10_6 : List ChainEdge :=
  []

theorem cert8_layer_34_10_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 34 [])
      LColor.r LColor.b cert8_seen_34_10_6 = cert8_layer_34_10_6 := by
  decide

theorem cert8_component_34_10_eq :
    closedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_34_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 34 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 27 cert8_seen_34_10_0 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_0 cert8_layer_34_10_0 26 cert8_layer_34_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 26 cert8_seen_34_10_1 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_1 cert8_layer_34_10_1 25 cert8_layer_34_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 25 cert8_seen_34_10_2 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_2 cert8_layer_34_10_2 24 cert8_layer_34_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 24 cert8_seen_34_10_3 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_3 cert8_layer_34_10_3 23 cert8_layer_34_10_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 23 cert8_seen_34_10_4 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_4 cert8_layer_34_10_4 22 cert8_layer_34_10_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 22 cert8_seen_34_10_5 = cert8_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_5 cert8_layer_34_10_5 21 cert8_layer_34_10_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 34 [])
      LColor.r LColor.b 21 cert8_seen_34_10_6 = cert8_component_34_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 34 []) LColor.r LColor.b
    cert8_seen_34_10_6 cert8_layer_34_10_6_eq 21

theorem cert8_step_34_10 :
    closedCollarIndexStepBool word fiber8 34 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_34_10)
    (by decide) (by decide)
    (by simpa [cert8_move_34_10] using cert8_component_34_10_eq)
    (by decide) (by decide) (by decide)

def cert8_move_35_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_35_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_seen_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_35_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_0 = cert8_layer_35_11_0 := by
  decide

def cert8_seen_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_35_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_1 = cert8_layer_35_11_1 := by
  decide

def cert8_seen_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_35_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_2 = cert8_layer_35_11_2 := by
  decide

def cert8_seen_35_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_35_11_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_35_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_3 = cert8_layer_35_11_3 := by
  decide

def cert8_seen_35_11_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_35_11_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_35_11_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_4 = cert8_layer_35_11_4 := by
  decide

def cert8_seen_35_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_35_11_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert8_layer_35_11_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_5 = cert8_layer_35_11_5 := by
  decide

def cert8_seen_35_11_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert8_layer_35_11_6 : List ChainEdge :=
  []

theorem cert8_layer_35_11_6_eq :
    closedCollarComponentLayer word (listGetD fiber8 35 [])
      LColor.r LColor.b cert8_seen_35_11_6 = cert8_layer_35_11_6 := by
  decide

theorem cert8_component_35_11_eq :
    closedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_35_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 35 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 27 cert8_seen_35_11_0 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_0 cert8_layer_35_11_0 26 cert8_layer_35_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 26 cert8_seen_35_11_1 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_1 cert8_layer_35_11_1 25 cert8_layer_35_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 25 cert8_seen_35_11_2 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_2 cert8_layer_35_11_2 24 cert8_layer_35_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 24 cert8_seen_35_11_3 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_3 cert8_layer_35_11_3 23 cert8_layer_35_11_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 23 cert8_seen_35_11_4 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_4 cert8_layer_35_11_4 22 cert8_layer_35_11_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 22 cert8_seen_35_11_5 = cert8_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_5 cert8_layer_35_11_5 21 cert8_layer_35_11_5_eq]
  change closeClosedCollarComponent word (listGetD fiber8 35 [])
      LColor.r LColor.b 21 cert8_seen_35_11_6 = cert8_component_35_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 35 []) LColor.r LColor.b
    cert8_seen_35_11_6 cert8_layer_35_11_6_eq 21

theorem cert8_step_35_11 :
    closedCollarIndexStepBool word fiber8 35 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_35_11)
    (by decide) (by decide)
    (by simpa [cert8_move_35_11] using cert8_component_35_11_eq)
    (by decide) (by decide) (by decide)

def cert8_move_36_24 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_36_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_36_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_36_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_36_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_24_0 = cert8_layer_36_24_0 := by
  decide

def cert8_seen_36_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_36_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_36_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_24_1 = cert8_layer_36_24_1 := by
  decide

def cert8_seen_36_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_36_24_2 : List ChainEdge :=
  []

theorem cert8_layer_36_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 36 [])
      LColor.b LColor.p cert8_seen_36_24_2 = cert8_layer_36_24_2 := by
  decide

theorem cert8_component_36_24_eq :
    closedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_36_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 27 cert8_seen_36_24_0 = cert8_component_36_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_24_0 cert8_layer_36_24_0 26 cert8_layer_36_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 26 cert8_seen_36_24_1 = cert8_component_36_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_24_1 cert8_layer_36_24_1 25 cert8_layer_36_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 36 [])
      LColor.b LColor.p 25 cert8_seen_36_24_2 = cert8_component_36_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 36 []) LColor.b LColor.p
    cert8_seen_36_24_2 cert8_layer_36_24_2_eq 25

theorem cert8_step_36_24 :
    closedCollarIndexStepBool word fiber8 36 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_36_24)
    (by decide) (by decide)
    (by simpa [cert8_move_36_24] using cert8_component_36_24_eq)
    (by decide) (by decide) (by decide)

def cert8_move_37_25 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_37_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_37_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_37_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_37_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_25_0 = cert8_layer_37_25_0 := by
  decide

def cert8_seen_37_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_37_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_37_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_25_1 = cert8_layer_37_25_1 := by
  decide

def cert8_seen_37_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_37_25_2 : List ChainEdge :=
  []

theorem cert8_layer_37_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 37 [])
      LColor.b LColor.p cert8_seen_37_25_2 = cert8_layer_37_25_2 := by
  decide

theorem cert8_component_37_25_eq :
    closedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_37_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 27 cert8_seen_37_25_0 = cert8_component_37_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_25_0 cert8_layer_37_25_0 26 cert8_layer_37_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 26 cert8_seen_37_25_1 = cert8_component_37_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_25_1 cert8_layer_37_25_1 25 cert8_layer_37_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 37 [])
      LColor.b LColor.p 25 cert8_seen_37_25_2 = cert8_component_37_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 37 []) LColor.b LColor.p
    cert8_seen_37_25_2 cert8_layer_37_25_2_eq 25

theorem cert8_step_37_25 :
    closedCollarIndexStepBool word fiber8 37 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_37_25)
    (by decide) (by decide)
    (by simpa [cert8_move_37_25] using cert8_component_37_25_eq)
    (by decide) (by decide) (by decide)

def cert8_move_38_26 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_38_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_38_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_38_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_38_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_26_0 = cert8_layer_38_26_0 := by
  decide

def cert8_seen_38_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_38_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_38_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_26_1 = cert8_layer_38_26_1 := by
  decide

def cert8_seen_38_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_38_26_2 : List ChainEdge :=
  []

theorem cert8_layer_38_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 38 [])
      LColor.b LColor.p cert8_seen_38_26_2 = cert8_layer_38_26_2 := by
  decide

theorem cert8_component_38_26_eq :
    closedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_38_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 27 cert8_seen_38_26_0 = cert8_component_38_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_26_0 cert8_layer_38_26_0 26 cert8_layer_38_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 26 cert8_seen_38_26_1 = cert8_component_38_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_26_1 cert8_layer_38_26_1 25 cert8_layer_38_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 38 [])
      LColor.b LColor.p 25 cert8_seen_38_26_2 = cert8_component_38_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 38 []) LColor.b LColor.p
    cert8_seen_38_26_2 cert8_layer_38_26_2_eq 25

theorem cert8_step_38_26 :
    closedCollarIndexStepBool word fiber8 38 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_38_26)
    (by decide) (by decide)
    (by simpa [cert8_move_38_26] using cert8_component_38_26_eq)
    (by decide) (by decide) (by decide)

def cert8_move_39_27 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_39_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_39_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_39_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_39_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_27_0 = cert8_layer_39_27_0 := by
  decide

def cert8_seen_39_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_39_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_39_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_27_1 = cert8_layer_39_27_1 := by
  decide

def cert8_seen_39_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_39_27_2 : List ChainEdge :=
  []

theorem cert8_layer_39_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 39 [])
      LColor.b LColor.p cert8_seen_39_27_2 = cert8_layer_39_27_2 := by
  decide

theorem cert8_component_39_27_eq :
    closedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_39_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 27 cert8_seen_39_27_0 = cert8_component_39_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_27_0 cert8_layer_39_27_0 26 cert8_layer_39_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 26 cert8_seen_39_27_1 = cert8_component_39_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_27_1 cert8_layer_39_27_1 25 cert8_layer_39_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 39 [])
      LColor.b LColor.p 25 cert8_seen_39_27_2 = cert8_component_39_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 39 []) LColor.b LColor.p
    cert8_seen_39_27_2 cert8_layer_39_27_2_eq 25

theorem cert8_step_39_27 :
    closedCollarIndexStepBool word fiber8 39 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_39_27)
    (by decide) (by decide)
    (by simpa [cert8_move_39_27] using cert8_component_39_27_eq)
    (by decide) (by decide) (by decide)

def cert8_move_40_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_40_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_40_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_40_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_40_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_28_0 = cert8_layer_40_28_0 := by
  decide

def cert8_seen_40_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_40_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_40_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_28_1 = cert8_layer_40_28_1 := by
  decide

def cert8_seen_40_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_40_28_2 : List ChainEdge :=
  []

theorem cert8_layer_40_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 40 [])
      LColor.b LColor.p cert8_seen_40_28_2 = cert8_layer_40_28_2 := by
  decide

theorem cert8_component_40_28_eq :
    closedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_40_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 27 cert8_seen_40_28_0 = cert8_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_28_0 cert8_layer_40_28_0 26 cert8_layer_40_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 26 cert8_seen_40_28_1 = cert8_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_28_1 cert8_layer_40_28_1 25 cert8_layer_40_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 40 [])
      LColor.b LColor.p 25 cert8_seen_40_28_2 = cert8_component_40_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 40 []) LColor.b LColor.p
    cert8_seen_40_28_2 cert8_layer_40_28_2_eq 25

theorem cert8_step_40_28 :
    closedCollarIndexStepBool word fiber8 40 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_40_28)
    (by decide) (by decide)
    (by simpa [cert8_move_40_28] using cert8_component_40_28_eq)
    (by decide) (by decide) (by decide)

def cert8_move_41_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert8_component_41_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_seen_41_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert8_layer_41_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert8_layer_41_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_29_0 = cert8_layer_41_29_0 := by
  decide

def cert8_seen_41_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert8_layer_41_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert8_layer_41_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_29_1 = cert8_layer_41_29_1 := by
  decide

def cert8_seen_41_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert8_layer_41_29_2 : List ChainEdge :=
  []

theorem cert8_layer_41_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 41 [])
      LColor.b LColor.p cert8_seen_41_29_2 = cert8_layer_41_29_2 := by
  decide

theorem cert8_component_41_29_eq :
    closedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert8_component_41_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 27 cert8_seen_41_29_0 = cert8_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_29_0 cert8_layer_41_29_0 26 cert8_layer_41_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 26 cert8_seen_41_29_1 = cert8_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_29_1 cert8_layer_41_29_1 25 cert8_layer_41_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 41 [])
      LColor.b LColor.p 25 cert8_seen_41_29_2 = cert8_component_41_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 41 []) LColor.b LColor.p
    cert8_seen_41_29_2 cert8_layer_41_29_2_eq 25

theorem cert8_step_41_29 :
    closedCollarIndexStepBool word fiber8 41 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_41_29)
    (by decide) (by decide)
    (by simpa [cert8_move_41_29] using cert8_component_41_29_eq)
    (by decide) (by decide) (by decide)

def cert8_move_42_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_42_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_42_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_42_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_42_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.r LColor.b cert8_seen_42_18_0 = cert8_layer_42_18_0 := by
  decide

def cert8_seen_42_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_42_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_42_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.r LColor.b cert8_seen_42_18_1 = cert8_layer_42_18_1 := by
  decide

def cert8_seen_42_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_42_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_42_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.r LColor.b cert8_seen_42_18_2 = cert8_layer_42_18_2 := by
  decide

def cert8_seen_42_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_42_18_3 : List ChainEdge :=
  []

theorem cert8_layer_42_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 42 [])
      LColor.r LColor.b cert8_seen_42_18_3 = cert8_layer_42_18_3 := by
  decide

theorem cert8_component_42_18_eq :
    closedCollarComponent word (listGetD fiber8 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_42_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.r LColor.b 27 cert8_seen_42_18_0 = cert8_component_42_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.r LColor.b
    cert8_seen_42_18_0 cert8_layer_42_18_0 26 cert8_layer_42_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.r LColor.b 26 cert8_seen_42_18_1 = cert8_component_42_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.r LColor.b
    cert8_seen_42_18_1 cert8_layer_42_18_1 25 cert8_layer_42_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.r LColor.b 25 cert8_seen_42_18_2 = cert8_component_42_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 42 []) LColor.r LColor.b
    cert8_seen_42_18_2 cert8_layer_42_18_2 24 cert8_layer_42_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 42 [])
      LColor.r LColor.b 24 cert8_seen_42_18_3 = cert8_component_42_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 42 []) LColor.r LColor.b
    cert8_seen_42_18_3 cert8_layer_42_18_3_eq 24

theorem cert8_step_42_18 :
    closedCollarIndexStepBool word fiber8 42 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_42_18)
    (by decide) (by decide)
    (by simpa [cert8_move_42_18] using cert8_component_42_18_eq)
    (by decide) (by decide) (by decide)

def cert8_move_43_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_43_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_43_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_43_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_43_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.r LColor.b cert8_seen_43_19_0 = cert8_layer_43_19_0 := by
  decide

def cert8_seen_43_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_43_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_43_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.r LColor.b cert8_seen_43_19_1 = cert8_layer_43_19_1 := by
  decide

def cert8_seen_43_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_43_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_43_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.r LColor.b cert8_seen_43_19_2 = cert8_layer_43_19_2 := by
  decide

def cert8_seen_43_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_43_19_3 : List ChainEdge :=
  []

theorem cert8_layer_43_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 43 [])
      LColor.r LColor.b cert8_seen_43_19_3 = cert8_layer_43_19_3 := by
  decide

theorem cert8_component_43_19_eq :
    closedCollarComponent word (listGetD fiber8 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_43_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.r LColor.b 27 cert8_seen_43_19_0 = cert8_component_43_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.r LColor.b
    cert8_seen_43_19_0 cert8_layer_43_19_0 26 cert8_layer_43_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.r LColor.b 26 cert8_seen_43_19_1 = cert8_component_43_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.r LColor.b
    cert8_seen_43_19_1 cert8_layer_43_19_1 25 cert8_layer_43_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.r LColor.b 25 cert8_seen_43_19_2 = cert8_component_43_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 43 []) LColor.r LColor.b
    cert8_seen_43_19_2 cert8_layer_43_19_2 24 cert8_layer_43_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 43 [])
      LColor.r LColor.b 24 cert8_seen_43_19_3 = cert8_component_43_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 43 []) LColor.r LColor.b
    cert8_seen_43_19_3 cert8_layer_43_19_3_eq 24

theorem cert8_step_43_19 :
    closedCollarIndexStepBool word fiber8 43 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_43_19)
    (by decide) (by decide)
    (by simpa [cert8_move_43_19] using cert8_component_43_19_eq)
    (by decide) (by decide) (by decide)

def cert8_move_44_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_44_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_44_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_44_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_44_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.b cert8_seen_44_20_0 = cert8_layer_44_20_0 := by
  decide

def cert8_seen_44_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_44_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_44_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.b cert8_seen_44_20_1 = cert8_layer_44_20_1 := by
  decide

def cert8_seen_44_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_44_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_44_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.b cert8_seen_44_20_2 = cert8_layer_44_20_2 := by
  decide

def cert8_seen_44_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_44_20_3 : List ChainEdge :=
  []

theorem cert8_layer_44_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 44 [])
      LColor.r LColor.b cert8_seen_44_20_3 = cert8_layer_44_20_3 := by
  decide

theorem cert8_component_44_20_eq :
    closedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_44_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 44 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.b 27 cert8_seen_44_20_0 = cert8_component_44_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 44 []) LColor.r LColor.b
    cert8_seen_44_20_0 cert8_layer_44_20_0 26 cert8_layer_44_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.b 26 cert8_seen_44_20_1 = cert8_component_44_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 44 []) LColor.r LColor.b
    cert8_seen_44_20_1 cert8_layer_44_20_1 25 cert8_layer_44_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.b 25 cert8_seen_44_20_2 = cert8_component_44_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 44 []) LColor.r LColor.b
    cert8_seen_44_20_2 cert8_layer_44_20_2 24 cert8_layer_44_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 44 [])
      LColor.r LColor.b 24 cert8_seen_44_20_3 = cert8_component_44_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 44 []) LColor.r LColor.b
    cert8_seen_44_20_3 cert8_layer_44_20_3_eq 24

theorem cert8_step_44_20 :
    closedCollarIndexStepBool word fiber8 44 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_44_20)
    (by decide) (by decide)
    (by simpa [cert8_move_44_20] using cert8_component_44_20_eq)
    (by decide) (by decide) (by decide)

def cert8_move_45_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_45_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_seen_45_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_45_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_45_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.b cert8_seen_45_21_0 = cert8_layer_45_21_0 := by
  decide

def cert8_seen_45_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_45_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert8_layer_45_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.b cert8_seen_45_21_1 = cert8_layer_45_21_1 := by
  decide

def cert8_seen_45_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert8_layer_45_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert8_layer_45_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.b cert8_seen_45_21_2 = cert8_layer_45_21_2 := by
  decide

def cert8_seen_45_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert8_layer_45_21_3 : List ChainEdge :=
  []

theorem cert8_layer_45_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 45 [])
      LColor.r LColor.b cert8_seen_45_21_3 = cert8_layer_45_21_3 := by
  decide

theorem cert8_component_45_21_eq :
    closedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_45_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 45 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.b 27 cert8_seen_45_21_0 = cert8_component_45_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 45 []) LColor.r LColor.b
    cert8_seen_45_21_0 cert8_layer_45_21_0 26 cert8_layer_45_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.b 26 cert8_seen_45_21_1 = cert8_component_45_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 45 []) LColor.r LColor.b
    cert8_seen_45_21_1 cert8_layer_45_21_1 25 cert8_layer_45_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.b 25 cert8_seen_45_21_2 = cert8_component_45_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 45 []) LColor.r LColor.b
    cert8_seen_45_21_2 cert8_layer_45_21_2 24 cert8_layer_45_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 45 [])
      LColor.r LColor.b 24 cert8_seen_45_21_3 = cert8_component_45_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 45 []) LColor.r LColor.b
    cert8_seen_45_21_3 cert8_layer_45_21_3_eq 24

theorem cert8_step_45_21 :
    closedCollarIndexStepBool word fiber8 45 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_45_21)
    (by decide) (by decide)
    (by simpa [cert8_move_45_21] using cert8_component_45_21_eq)
    (by decide) (by decide) (by decide)

def cert8_move_46_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_46_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_seen_46_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_46_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_46_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_0 = cert8_layer_46_22_0 := by
  decide

def cert8_seen_46_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_46_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_46_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_1 = cert8_layer_46_22_1 := by
  decide

def cert8_seen_46_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_46_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_46_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_2 = cert8_layer_46_22_2 := by
  decide

def cert8_seen_46_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_46_22_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_46_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_3 = cert8_layer_46_22_3 := by
  decide

def cert8_seen_46_22_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_46_22_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_46_22_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_4 = cert8_layer_46_22_4 := by
  decide

def cert8_seen_46_22_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_46_22_5 : List ChainEdge :=
  []

theorem cert8_layer_46_22_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 46 [])
      LColor.r LColor.b cert8_seen_46_22_5 = cert8_layer_46_22_5 := by
  decide

theorem cert8_component_46_22_eq :
    closedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_46_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 46 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 27 cert8_seen_46_22_0 = cert8_component_46_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_0 cert8_layer_46_22_0 26 cert8_layer_46_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 26 cert8_seen_46_22_1 = cert8_component_46_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_1 cert8_layer_46_22_1 25 cert8_layer_46_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 25 cert8_seen_46_22_2 = cert8_component_46_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_2 cert8_layer_46_22_2 24 cert8_layer_46_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 24 cert8_seen_46_22_3 = cert8_component_46_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_3 cert8_layer_46_22_3 23 cert8_layer_46_22_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 23 cert8_seen_46_22_4 = cert8_component_46_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_4 cert8_layer_46_22_4 22 cert8_layer_46_22_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 46 [])
      LColor.r LColor.b 22 cert8_seen_46_22_5 = cert8_component_46_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 46 []) LColor.r LColor.b
    cert8_seen_46_22_5 cert8_layer_46_22_5_eq 22

theorem cert8_step_46_22 :
    closedCollarIndexStepBool word fiber8 46 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_46_22)
    (by decide) (by decide)
    (by simpa [cert8_move_46_22] using cert8_component_46_22_eq)
    (by decide) (by decide) (by decide)

def cert8_move_47_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert8_component_47_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_seen_47_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert8_layer_47_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert8_layer_47_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_0 = cert8_layer_47_23_0 := by
  decide

def cert8_seen_47_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert8_layer_47_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert8_layer_47_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_1 = cert8_layer_47_23_1 := by
  decide

def cert8_seen_47_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert8_layer_47_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert8_layer_47_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_2 = cert8_layer_47_23_2 := by
  decide

def cert8_seen_47_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert8_layer_47_23_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert8_layer_47_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_3 = cert8_layer_47_23_3 := by
  decide

def cert8_seen_47_23_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert8_layer_47_23_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert8_layer_47_23_4_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_4 = cert8_layer_47_23_4 := by
  decide

def cert8_seen_47_23_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert8_layer_47_23_5 : List ChainEdge :=
  []

theorem cert8_layer_47_23_5_eq :
    closedCollarComponentLayer word (listGetD fiber8 47 [])
      LColor.r LColor.b cert8_seen_47_23_5 = cert8_layer_47_23_5 := by
  decide

theorem cert8_component_47_23_eq :
    closedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert8_component_47_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber8 47 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 27 cert8_seen_47_23_0 = cert8_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_0 cert8_layer_47_23_0 26 cert8_layer_47_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 26 cert8_seen_47_23_1 = cert8_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_1 cert8_layer_47_23_1 25 cert8_layer_47_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 25 cert8_seen_47_23_2 = cert8_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_2 cert8_layer_47_23_2 24 cert8_layer_47_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 24 cert8_seen_47_23_3 = cert8_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_3 cert8_layer_47_23_3 23 cert8_layer_47_23_3_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 23 cert8_seen_47_23_4 = cert8_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_4 cert8_layer_47_23_4 22 cert8_layer_47_23_4_eq]
  change closeClosedCollarComponent word (listGetD fiber8 47 [])
      LColor.r LColor.b 22 cert8_seen_47_23_5 = cert8_component_47_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber8 47 []) LColor.r LColor.b
    cert8_seen_47_23_5 cert8_layer_47_23_5_eq 22

theorem cert8_step_47_23 :
    closedCollarIndexStepBool word fiber8 47 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert8_move_47_23)
    (by decide) (by decide)
    (by simpa [cert8_move_47_23] using cert8_component_47_23_eq)
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
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_2_0, cert8_step_0_2]

theorem cert8_row_3 :
    closedCollarParentIndexValid word fiber8 cert8.parents 3 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_3_1, cert8_step_1_3]

theorem cert8_row_4 :
    closedCollarParentIndexValid word fiber8 cert8.parents 4 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_4_1, cert8_step_1_4]

theorem cert8_row_5 :
    closedCollarParentIndexValid word fiber8 cert8.parents 5 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_5_0, cert8_step_0_5]

theorem cert8_row_6 :
    closedCollarParentIndexValid word fiber8 cert8.parents 6 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_6_0, cert8_step_0_6]

theorem cert8_row_7 :
    closedCollarParentIndexValid word fiber8 cert8.parents 7 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_7_1, cert8_step_1_7]

theorem cert8_row_8 :
    closedCollarParentIndexValid word fiber8 cert8.parents 8 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_8_2, cert8_step_2_8]

theorem cert8_row_9 :
    closedCollarParentIndexValid word fiber8 cert8.parents 9 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_9_3, cert8_step_3_9]

theorem cert8_row_10 :
    closedCollarParentIndexValid word fiber8 cert8.parents 10 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_10_4, cert8_step_4_10]

theorem cert8_row_11 :
    closedCollarParentIndexValid word fiber8 cert8.parents 11 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_11_5, cert8_step_5_11]

theorem cert8_row_12 :
    closedCollarParentIndexValid word fiber8 cert8.parents 12 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_12_6, cert8_step_6_12]

theorem cert8_row_13 :
    closedCollarParentIndexValid word fiber8 cert8.parents 13 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_13_7, cert8_step_7_13]

theorem cert8_row_14 :
    closedCollarParentIndexValid word fiber8 cert8.parents 14 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_14_8, cert8_step_8_14]

theorem cert8_row_15 :
    closedCollarParentIndexValid word fiber8 cert8.parents 15 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_15_9, cert8_step_9_15]

theorem cert8_row_16 :
    closedCollarParentIndexValid word fiber8 cert8.parents 16 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_16_10, cert8_step_10_16]

theorem cert8_row_17 :
    closedCollarParentIndexValid word fiber8 cert8.parents 17 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_17_11, cert8_step_11_17]

theorem cert8_row_18 :
    closedCollarParentIndexValid word fiber8 cert8.parents 18 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_18_0, cert8_step_0_18]

theorem cert8_row_19 :
    closedCollarParentIndexValid word fiber8 cert8.parents 19 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_19_1, cert8_step_1_19]

theorem cert8_row_20 :
    closedCollarParentIndexValid word fiber8 cert8.parents 20 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_20_2, cert8_step_2_20]

theorem cert8_row_21 :
    closedCollarParentIndexValid word fiber8 cert8.parents 21 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_21_3, cert8_step_3_21]

theorem cert8_row_22 :
    closedCollarParentIndexValid word fiber8 cert8.parents 22 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_22_4, cert8_step_4_22]

theorem cert8_row_23 :
    closedCollarParentIndexValid word fiber8 cert8.parents 23 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_23_5, cert8_step_5_23]

theorem cert8_row_24 :
    closedCollarParentIndexValid word fiber8 cert8.parents 24 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_24_0, cert8_step_0_24]

theorem cert8_row_25 :
    closedCollarParentIndexValid word fiber8 cert8.parents 25 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_25_1, cert8_step_1_25]

theorem cert8_row_26 :
    closedCollarParentIndexValid word fiber8 cert8.parents 26 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_26_2, cert8_step_2_26]

theorem cert8_row_27 :
    closedCollarParentIndexValid word fiber8 cert8.parents 27 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_27_3, cert8_step_3_27]

theorem cert8_row_28 :
    closedCollarParentIndexValid word fiber8 cert8.parents 28 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_28_4, cert8_step_4_28]

theorem cert8_row_29 :
    closedCollarParentIndexValid word fiber8 cert8.parents 29 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_29_5, cert8_step_5_29]

theorem cert8_row_30 :
    closedCollarParentIndexValid word fiber8 cert8.parents 30 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_30_6, cert8_step_6_30]

theorem cert8_row_31 :
    closedCollarParentIndexValid word fiber8 cert8.parents 31 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_31_7, cert8_step_7_31]

theorem cert8_row_32 :
    closedCollarParentIndexValid word fiber8 cert8.parents 32 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_32_8, cert8_step_8_32]

theorem cert8_row_33 :
    closedCollarParentIndexValid word fiber8 cert8.parents 33 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_33_9, cert8_step_9_33]

theorem cert8_row_34 :
    closedCollarParentIndexValid word fiber8 cert8.parents 34 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_34_10, cert8_step_10_34]

theorem cert8_row_35 :
    closedCollarParentIndexValid word fiber8 cert8.parents 35 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_35_11, cert8_step_11_35]

theorem cert8_row_36 :
    closedCollarParentIndexValid word fiber8 cert8.parents 36 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_36_24, cert8_step_24_36]

theorem cert8_row_37 :
    closedCollarParentIndexValid word fiber8 cert8.parents 37 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_37_25, cert8_step_25_37]

theorem cert8_row_38 :
    closedCollarParentIndexValid word fiber8 cert8.parents 38 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_38_26, cert8_step_26_38]

theorem cert8_row_39 :
    closedCollarParentIndexValid word fiber8 cert8.parents 39 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_39_27, cert8_step_27_39]

theorem cert8_row_40 :
    closedCollarParentIndexValid word fiber8 cert8.parents 40 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_40_28, cert8_step_28_40]

theorem cert8_row_41 :
    closedCollarParentIndexValid word fiber8 cert8.parents 41 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_41_29, cert8_step_29_41]

theorem cert8_row_42 :
    closedCollarParentIndexValid word fiber8 cert8.parents 42 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_42_18, cert8_step_18_42]

theorem cert8_row_43 :
    closedCollarParentIndexValid word fiber8 cert8.parents 43 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_43_19, cert8_step_19_43]

theorem cert8_row_44 :
    closedCollarParentIndexValid word fiber8 cert8.parents 44 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_44_20, cert8_step_20_44]

theorem cert8_row_45 :
    closedCollarParentIndexValid word fiber8 cert8.parents 45 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_45_21, cert8_step_21_45]

theorem cert8_row_46 :
    closedCollarParentIndexValid word fiber8 cert8.parents 46 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_46_22, cert8_step_22_46]

theorem cert8_row_47 :
    closedCollarParentIndexValid word fiber8 cert8.parents 47 = true := by
  have cert8_fiber_length : fiber8.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert8, listGetD, cert8_fiber_length, cert8_step_47_23, cert8_step_23_47]

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


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
