import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast76 : List TauState :=
  [stateAt 32, stateAt 40, stateAt 48, stateAt 56, stateAt 132, stateAt 140, stateAt 148, stateAt 156]

theorem keyedLast76_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.b, LColor.b]) =
      keyedLast76 := by
  decide

def fiber76OuterChunks : List (List (List TauState)) :=
[
  []
, []
, []
, []
, []
, [
  [stateAt 88, stateAt 80, stateAt 156]
, [stateAt 88, stateAt 81, stateAt 148]
, [stateAt 88, stateAt 82, stateAt 140]
, [stateAt 88, stateAt 83, stateAt 132]
, [stateAt 88, stateAt 100, stateAt 40]
, [stateAt 88, stateAt 101, stateAt 32]
, [stateAt 88, stateAt 102, stateAt 56]
, [stateAt 88, stateAt 103, stateAt 48]
, [stateAt 89, stateAt 88, stateAt 156]
, [stateAt 89, stateAt 89, stateAt 148]
, [stateAt 89, stateAt 90, stateAt 140]
, [stateAt 89, stateAt 91, stateAt 132]
, [stateAt 89, stateAt 108, stateAt 40]
, [stateAt 89, stateAt 109, stateAt 32]
, [stateAt 89, stateAt 110, stateAt 56]
, [stateAt 89, stateAt 111, stateAt 48]
, [stateAt 90, stateAt 16, stateAt 156]
, [stateAt 90, stateAt 17, stateAt 148]
, [stateAt 90, stateAt 18, stateAt 140]
, [stateAt 90, stateAt 19, stateAt 132]
, [stateAt 91, stateAt 24, stateAt 156]
, [stateAt 91, stateAt 25, stateAt 148]
, [stateAt 91, stateAt 26, stateAt 140]
, [stateAt 91, stateAt 27, stateAt 132]
]
, [
  [stateAt 108, stateAt 180, stateAt 40]
, [stateAt 108, stateAt 181, stateAt 32]
, [stateAt 108, stateAt 182, stateAt 56]
, [stateAt 108, stateAt 183, stateAt 48]
, [stateAt 109, stateAt 188, stateAt 40]
, [stateAt 109, stateAt 189, stateAt 32]
, [stateAt 109, stateAt 190, stateAt 56]
, [stateAt 109, stateAt 191, stateAt 48]
, [stateAt 110, stateAt 64, stateAt 156]
, [stateAt 110, stateAt 65, stateAt 148]
, [stateAt 110, stateAt 66, stateAt 140]
, [stateAt 110, stateAt 67, stateAt 132]
, [stateAt 110, stateAt 116, stateAt 40]
, [stateAt 110, stateAt 117, stateAt 32]
, [stateAt 110, stateAt 118, stateAt 56]
, [stateAt 110, stateAt 119, stateAt 48]
, [stateAt 111, stateAt 72, stateAt 156]
, [stateAt 111, stateAt 73, stateAt 148]
, [stateAt 111, stateAt 74, stateAt 140]
, [stateAt 111, stateAt 75, stateAt 132]
, [stateAt 111, stateAt 124, stateAt 40]
, [stateAt 111, stateAt 125, stateAt 32]
, [stateAt 111, stateAt 126, stateAt 56]
, [stateAt 111, stateAt 127, stateAt 48]
]
, []
, []
, []
, []
, []
]

def fiber76 : List (List TauState) :=
  fiber76OuterChunks.flatten

theorem fiber76_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 0 []) =
      listGetD fiber76OuterChunks 0 [] := by
  decide

theorem fiber76_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 1 []) =
      listGetD fiber76OuterChunks 1 [] := by
  decide

theorem fiber76_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 2 []) =
      listGetD fiber76OuterChunks 2 [] := by
  decide

theorem fiber76_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 3 []) =
      listGetD fiber76OuterChunks 3 [] := by
  decide

theorem fiber76_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 4 []) =
      listGetD fiber76OuterChunks 4 [] := by
  decide

theorem fiber76_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 5 []) =
      listGetD fiber76OuterChunks 5 [] := by
  decide

theorem fiber76_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 6 []) =
      listGetD fiber76OuterChunks 6 [] := by
  decide

theorem fiber76_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 7 []) =
      listGetD fiber76OuterChunks 7 [] := by
  decide

theorem fiber76_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 8 []) =
      listGetD fiber76OuterChunks 8 [] := by
  decide

theorem fiber76_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 9 []) =
      listGetD fiber76OuterChunks 9 [] := by
  decide

theorem fiber76_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 10 []) =
      listGetD fiber76OuterChunks 10 [] := by
  decide

theorem fiber76_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks 11 []) =
      listGetD fiber76OuterChunks 11 [] := by
  decide

theorem fiber76_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast76
        (listGetD tauStateChunks idx []) =
      listGetD fiber76OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber76_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber76_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber76_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber76_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber76_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber76_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber76_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber76_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber76_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber76_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber76_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber76_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber76_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast76 =
      fiber76 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast76 tauStateChunks fiber76OuterChunks
    tauStateChunks_eq (by rfl) fiber76_outer_get
  simpa [fiber76] using h

theorem fiber76_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.b, LColor.b] = fiber76 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.b, LColor.b] keyedLast76_eq
  exact hfrom.trans fiber76_keyedFrom_eq

theorem fiber76_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.b, LColor.b] = fiber76 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.b, LColor.b]
  exact hfast.trans fiber76_keyed_eq

def cert76 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.b, LColor.b],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 0, 1, 2, 7, 1, 0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 18, 27, 17, 16, 44, 45, 46, 47, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7] }

def cert76_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert76_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert76_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert76_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert76_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_1_0 = cert76_layer_0_1_0 := by
  decide

def cert76_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert76_layer_0_1_1 : List ChainEdge :=
  []

theorem cert76_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_1_1 = cert76_layer_0_1_1 := by
  decide

theorem cert76_component_0_1_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert76_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 27 cert76_seen_0_1_0 = cert76_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_1_0 cert76_layer_0_1_0 26 cert76_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 26 cert76_seen_0_1_1 = cert76_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_1_1 cert76_layer_0_1_1_eq 26

theorem cert76_step_0_1 :
    closedCollarIndexStepBool word fiber76 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_1)
    (by decide) (by decide)
    (by simpa [cert76_move_0_1] using cert76_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_2_0 = cert76_layer_0_2_0 := by
  decide

def cert76_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_0_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_2_1 = cert76_layer_0_2_1 := by
  decide

def cert76_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_0_2_2 : List ChainEdge :=
  []

theorem cert76_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_2_2 = cert76_layer_0_2_2 := by
  decide

theorem cert76_component_0_2_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert76_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 27 cert76_seen_0_2_0 = cert76_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_2_0 cert76_layer_0_2_0 26 cert76_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 26 cert76_seen_0_2_1 = cert76_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_2_1 cert76_layer_0_2_1 25 cert76_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 25 cert76_seen_0_2_2 = cert76_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_2_2 cert76_layer_0_2_2_eq 25

theorem cert76_step_0_2 :
    closedCollarIndexStepBool word fiber76 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_2)
    (by decide) (by decide)
    (by simpa [cert76_move_0_2] using cert76_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_0_7 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_0_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_0_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_0_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_7_0 = cert76_layer_0_7_0 := by
  decide

def cert76_seen_0_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_0_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_0_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_7_1 = cert76_layer_0_7_1 := by
  decide

def cert76_seen_0_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_0_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_0_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_7_2 = cert76_layer_0_7_2 := by
  decide

def cert76_seen_0_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_0_7_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_0_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_7_3 = cert76_layer_0_7_3 := by
  decide

def cert76_seen_0_7_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_0_7_4 : List ChainEdge :=
  []

theorem cert76_layer_0_7_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_7_4 = cert76_layer_0_7_4 := by
  decide

theorem cert76_component_0_7_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_0_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 27 cert76_seen_0_7_0 = cert76_component_0_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_7_0 cert76_layer_0_7_0 26 cert76_layer_0_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 26 cert76_seen_0_7_1 = cert76_component_0_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_7_1 cert76_layer_0_7_1 25 cert76_layer_0_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 25 cert76_seen_0_7_2 = cert76_component_0_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_7_2 cert76_layer_0_7_2 24 cert76_layer_0_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 24 cert76_seen_0_7_3 = cert76_component_0_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_7_3 cert76_layer_0_7_3 23 cert76_layer_0_7_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 23 cert76_seen_0_7_4 = cert76_component_0_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_7_4 cert76_layer_0_7_4_eq 23

theorem cert76_step_0_7 :
    closedCollarIndexStepBool word fiber76 0 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_7)
    (by decide) (by decide)
    (by simpa [cert76_move_0_7] using cert76_component_0_7_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_0_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_0_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_0_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_0_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_8_0 = cert76_layer_0_8_0 := by
  decide

def cert76_seen_0_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_0_8_1 : List ChainEdge :=
  []

theorem cert76_layer_0_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.b LColor.p cert76_seen_0_8_1 = cert76_layer_0_8_1 := by
  decide

theorem cert76_component_0_8_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_0_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 27 cert76_seen_0_8_0 = cert76_component_0_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_8_0 cert76_layer_0_8_0 26 cert76_layer_0_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.b LColor.p 26 cert76_seen_0_8_1 = cert76_component_0_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.b LColor.p
    cert76_seen_0_8_1 cert76_layer_0_8_1_eq 26

theorem cert76_step_0_8 :
    closedCollarIndexStepBool word fiber76 0 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_8)
    (by decide) (by decide)
    (by simpa [cert76_move_0_8] using cert76_component_0_8_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_0_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_0_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_16_0 = cert76_layer_0_16_0 := by
  decide

def cert76_seen_0_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_0_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_0_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_16_1 = cert76_layer_0_16_1 := by
  decide

def cert76_seen_0_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_0_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_0_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_16_2 = cert76_layer_0_16_2 := by
  decide

def cert76_seen_0_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_0_16_3 : List ChainEdge :=
  []

theorem cert76_layer_0_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.b cert76_seen_0_16_3 = cert76_layer_0_16_3 := by
  decide

theorem cert76_component_0_16_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_0_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 27 cert76_seen_0_16_0 = cert76_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_16_0 cert76_layer_0_16_0 26 cert76_layer_0_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 26 cert76_seen_0_16_1 = cert76_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_16_1 cert76_layer_0_16_1 25 cert76_layer_0_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 25 cert76_seen_0_16_2 = cert76_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_16_2 cert76_layer_0_16_2 24 cert76_layer_0_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.b 24 cert76_seen_0_16_3 = cert76_component_0_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.b
    cert76_seen_0_16_3 cert76_layer_0_16_3_eq 24

theorem cert76_step_0_16 :
    closedCollarIndexStepBool word fiber76 0 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_16)
    (by decide) (by decide)
    (by simpa [cert76_move_0_16] using cert76_component_0_16_eq)
    (by decide) (by decide) (by decide)

def cert76_move_0_40 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_0_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_0_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_0_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_0_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_40_0 = cert76_layer_0_40_0 := by
  decide

def cert76_seen_0_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_0_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_0_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_40_1 = cert76_layer_0_40_1 := by
  decide

def cert76_seen_0_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_0_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_0_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_40_2 = cert76_layer_0_40_2 := by
  decide

def cert76_seen_0_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_0_40_3 : List ChainEdge :=
  []

theorem cert76_layer_0_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 0 [])
      LColor.r LColor.p cert76_seen_0_40_3 = cert76_layer_0_40_3 := by
  decide

theorem cert76_component_0_40_eq :
    closedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_0_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 27 cert76_seen_0_40_0 = cert76_component_0_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_40_0 cert76_layer_0_40_0 26 cert76_layer_0_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 26 cert76_seen_0_40_1 = cert76_component_0_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_40_1 cert76_layer_0_40_1 25 cert76_layer_0_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 25 cert76_seen_0_40_2 = cert76_component_0_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_40_2 cert76_layer_0_40_2 24 cert76_layer_0_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 0 [])
      LColor.r LColor.p 24 cert76_seen_0_40_3 = cert76_component_0_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 0 []) LColor.r LColor.p
    cert76_seen_0_40_3 cert76_layer_0_40_3_eq 24

theorem cert76_step_0_40 :
    closedCollarIndexStepBool word fiber76 0 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_0_40)
    (by decide) (by decide)
    (by simpa [cert76_move_0_40] using cert76_component_0_40_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert76_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert76_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert76_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert76_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_0_0 = cert76_layer_1_0_0 := by
  decide

def cert76_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert76_layer_1_0_1 : List ChainEdge :=
  []

theorem cert76_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_0_1 = cert76_layer_1_0_1 := by
  decide

theorem cert76_component_1_0_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert76_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 27 cert76_seen_1_0_0 = cert76_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_0_0 cert76_layer_1_0_0 26 cert76_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 26 cert76_seen_1_0_1 = cert76_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_0_1 cert76_layer_1_0_1_eq 26

theorem cert76_step_1_0 :
    closedCollarIndexStepBool word fiber76 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_0)
    (by decide) (by decide)
    (by simpa [cert76_move_1_0] using cert76_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_3_0 = cert76_layer_1_3_0 := by
  decide

def cert76_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_1_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_3_1 = cert76_layer_1_3_1 := by
  decide

def cert76_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_1_3_2 : List ChainEdge :=
  []

theorem cert76_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_3_2 = cert76_layer_1_3_2 := by
  decide

theorem cert76_component_1_3_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert76_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 27 cert76_seen_1_3_0 = cert76_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_3_0 cert76_layer_1_3_0 26 cert76_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 26 cert76_seen_1_3_1 = cert76_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_3_1 cert76_layer_1_3_1 25 cert76_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 25 cert76_seen_1_3_2 = cert76_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_3_2 cert76_layer_1_3_2_eq 25

theorem cert76_step_1_3 :
    closedCollarIndexStepBool word fiber76 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_3)
    (by decide) (by decide)
    (by simpa [cert76_move_1_3] using cert76_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_1_6 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_1_6_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_1_6_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_1_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_6_0 = cert76_layer_1_6_0 := by
  decide

def cert76_seen_1_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_1_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_1_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_6_1 = cert76_layer_1_6_1 := by
  decide

def cert76_seen_1_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_1_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_1_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_6_2 = cert76_layer_1_6_2 := by
  decide

def cert76_seen_1_6_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_1_6_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_1_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_6_3 = cert76_layer_1_6_3 := by
  decide

def cert76_seen_1_6_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_1_6_4 : List ChainEdge :=
  []

theorem cert76_layer_1_6_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_6_4 = cert76_layer_1_6_4 := by
  decide

theorem cert76_component_1_6_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_1_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 27 cert76_seen_1_6_0 = cert76_component_1_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_6_0 cert76_layer_1_6_0 26 cert76_layer_1_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 26 cert76_seen_1_6_1 = cert76_component_1_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_6_1 cert76_layer_1_6_1 25 cert76_layer_1_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 25 cert76_seen_1_6_2 = cert76_component_1_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_6_2 cert76_layer_1_6_2 24 cert76_layer_1_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 24 cert76_seen_1_6_3 = cert76_component_1_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_6_3 cert76_layer_1_6_3 23 cert76_layer_1_6_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 23 cert76_seen_1_6_4 = cert76_component_1_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_6_4 cert76_layer_1_6_4_eq 23

theorem cert76_step_1_6 :
    closedCollarIndexStepBool word fiber76 1 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_6)
    (by decide) (by decide)
    (by simpa [cert76_move_1_6] using cert76_component_1_6_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_1_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_1_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_1_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_1_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_9_0 = cert76_layer_1_9_0 := by
  decide

def cert76_seen_1_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_1_9_1 : List ChainEdge :=
  []

theorem cert76_layer_1_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.b LColor.p cert76_seen_1_9_1 = cert76_layer_1_9_1 := by
  decide

theorem cert76_component_1_9_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_1_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 27 cert76_seen_1_9_0 = cert76_component_1_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_9_0 cert76_layer_1_9_0 26 cert76_layer_1_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.b LColor.p 26 cert76_seen_1_9_1 = cert76_component_1_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.b LColor.p
    cert76_seen_1_9_1 cert76_layer_1_9_1_eq 26

theorem cert76_step_1_9 :
    closedCollarIndexStepBool word fiber76 1 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_9)
    (by decide) (by decide)
    (by simpa [cert76_move_1_9] using cert76_component_1_9_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_1_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_1_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_17_0 = cert76_layer_1_17_0 := by
  decide

def cert76_seen_1_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_1_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_1_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_17_1 = cert76_layer_1_17_1 := by
  decide

def cert76_seen_1_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_1_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_1_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_17_2 = cert76_layer_1_17_2 := by
  decide

def cert76_seen_1_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_1_17_3 : List ChainEdge :=
  []

theorem cert76_layer_1_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.b cert76_seen_1_17_3 = cert76_layer_1_17_3 := by
  decide

theorem cert76_component_1_17_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_1_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 27 cert76_seen_1_17_0 = cert76_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_17_0 cert76_layer_1_17_0 26 cert76_layer_1_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 26 cert76_seen_1_17_1 = cert76_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_17_1 cert76_layer_1_17_1 25 cert76_layer_1_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 25 cert76_seen_1_17_2 = cert76_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_17_2 cert76_layer_1_17_2 24 cert76_layer_1_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.b 24 cert76_seen_1_17_3 = cert76_component_1_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.b
    cert76_seen_1_17_3 cert76_layer_1_17_3_eq 24

theorem cert76_step_1_17 :
    closedCollarIndexStepBool word fiber76 1 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_17)
    (by decide) (by decide)
    (by simpa [cert76_move_1_17] using cert76_component_1_17_eq)
    (by decide) (by decide) (by decide)

def cert76_move_1_41 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_1_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_1_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_1_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_1_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_41_0 = cert76_layer_1_41_0 := by
  decide

def cert76_seen_1_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_1_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_1_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_41_1 = cert76_layer_1_41_1 := by
  decide

def cert76_seen_1_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_1_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_1_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_41_2 = cert76_layer_1_41_2 := by
  decide

def cert76_seen_1_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_1_41_3 : List ChainEdge :=
  []

theorem cert76_layer_1_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 1 [])
      LColor.r LColor.p cert76_seen_1_41_3 = cert76_layer_1_41_3 := by
  decide

theorem cert76_component_1_41_eq :
    closedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_1_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 27 cert76_seen_1_41_0 = cert76_component_1_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_41_0 cert76_layer_1_41_0 26 cert76_layer_1_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 26 cert76_seen_1_41_1 = cert76_component_1_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_41_1 cert76_layer_1_41_1 25 cert76_layer_1_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 25 cert76_seen_1_41_2 = cert76_component_1_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_41_2 cert76_layer_1_41_2 24 cert76_layer_1_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 1 [])
      LColor.r LColor.p 24 cert76_seen_1_41_3 = cert76_component_1_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 1 []) LColor.r LColor.p
    cert76_seen_1_41_3 cert76_layer_1_41_3_eq 24

theorem cert76_step_1_41 :
    closedCollarIndexStepBool word fiber76 1 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_1_41)
    (by decide) (by decide)
    (by simpa [cert76_move_1_41] using cert76_component_1_41_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_0_0 = cert76_layer_2_0_0 := by
  decide

def cert76_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_2_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_0_1 = cert76_layer_2_0_1 := by
  decide

def cert76_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_2_0_2 : List ChainEdge :=
  []

theorem cert76_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_0_2 = cert76_layer_2_0_2 := by
  decide

theorem cert76_component_2_0_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert76_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 27 cert76_seen_2_0_0 = cert76_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_0_0 cert76_layer_2_0_0 26 cert76_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 26 cert76_seen_2_0_1 = cert76_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_0_1 cert76_layer_2_0_1 25 cert76_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 25 cert76_seen_2_0_2 = cert76_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_0_2 cert76_layer_2_0_2_eq 25

theorem cert76_step_2_0 :
    closedCollarIndexStepBool word fiber76 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_0)
    (by decide) (by decide)
    (by simpa [cert76_move_2_0] using cert76_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_2_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_seen_2_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_2_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_4_0 = cert76_layer_2_4_0 := by
  decide

def cert76_seen_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_4_1 = cert76_layer_2_4_1 := by
  decide

def cert76_seen_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_2_4_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_4_2 = cert76_layer_2_4_2 := by
  decide

def cert76_seen_2_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_2_4_3 : List ChainEdge :=
  []

theorem cert76_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_4_3 = cert76_layer_2_4_3 := by
  decide

theorem cert76_component_2_4_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 27 cert76_seen_2_4_0 = cert76_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_4_0 cert76_layer_2_4_0 26 cert76_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 26 cert76_seen_2_4_1 = cert76_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_4_1 cert76_layer_2_4_1 25 cert76_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 25 cert76_seen_2_4_2 = cert76_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_4_2 cert76_layer_2_4_2 24 cert76_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 24 cert76_seen_2_4_3 = cert76_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_4_3 cert76_layer_2_4_3_eq 24

theorem cert76_step_2_4 :
    closedCollarIndexStepBool word fiber76 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_4)
    (by decide) (by decide)
    (by simpa [cert76_move_2_4] using cert76_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_2_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_2_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_2_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_2_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.b LColor.p cert76_seen_2_10_0 = cert76_layer_2_10_0 := by
  decide

def cert76_seen_2_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_2_10_1 : List ChainEdge :=
  []

theorem cert76_layer_2_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.b LColor.p cert76_seen_2_10_1 = cert76_layer_2_10_1 := by
  decide

theorem cert76_component_2_10_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_2_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.b LColor.p 27 cert76_seen_2_10_0 = cert76_component_2_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.b LColor.p
    cert76_seen_2_10_0 cert76_layer_2_10_0 26 cert76_layer_2_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.b LColor.p 26 cert76_seen_2_10_1 = cert76_component_2_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.b LColor.p
    cert76_seen_2_10_1 cert76_layer_2_10_1_eq 26

theorem cert76_step_2_10 :
    closedCollarIndexStepBool word fiber76 2 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_10)
    (by decide) (by decide)
    (by simpa [cert76_move_2_10] using cert76_component_2_10_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_2_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_2_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_18_0 = cert76_layer_2_18_0 := by
  decide

def cert76_seen_2_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_2_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_2_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_18_1 = cert76_layer_2_18_1 := by
  decide

def cert76_seen_2_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_2_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_2_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_18_2 = cert76_layer_2_18_2 := by
  decide

def cert76_seen_2_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_2_18_3 : List ChainEdge :=
  []

theorem cert76_layer_2_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.b cert76_seen_2_18_3 = cert76_layer_2_18_3 := by
  decide

theorem cert76_component_2_18_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_2_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 27 cert76_seen_2_18_0 = cert76_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_18_0 cert76_layer_2_18_0 26 cert76_layer_2_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 26 cert76_seen_2_18_1 = cert76_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_18_1 cert76_layer_2_18_1 25 cert76_layer_2_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 25 cert76_seen_2_18_2 = cert76_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_18_2 cert76_layer_2_18_2 24 cert76_layer_2_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.b 24 cert76_seen_2_18_3 = cert76_component_2_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.r LColor.b
    cert76_seen_2_18_3 cert76_layer_2_18_3_eq 24

theorem cert76_step_2_18 :
    closedCollarIndexStepBool word fiber76 2 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_18)
    (by decide) (by decide)
    (by simpa [cert76_move_2_18] using cert76_component_2_18_eq)
    (by decide) (by decide) (by decide)

def cert76_move_2_42 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_2_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_2_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_2_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_2_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_42_0 = cert76_layer_2_42_0 := by
  decide

def cert76_seen_2_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_2_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_2_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_42_1 = cert76_layer_2_42_1 := by
  decide

def cert76_seen_2_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_2_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_2_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_42_2 = cert76_layer_2_42_2 := by
  decide

def cert76_seen_2_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_2_42_3 : List ChainEdge :=
  []

theorem cert76_layer_2_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 2 [])
      LColor.r LColor.p cert76_seen_2_42_3 = cert76_layer_2_42_3 := by
  decide

theorem cert76_component_2_42_eq :
    closedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_2_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 27 cert76_seen_2_42_0 = cert76_component_2_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_42_0 cert76_layer_2_42_0 26 cert76_layer_2_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 26 cert76_seen_2_42_1 = cert76_component_2_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_42_1 cert76_layer_2_42_1 25 cert76_layer_2_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 25 cert76_seen_2_42_2 = cert76_component_2_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_42_2 cert76_layer_2_42_2 24 cert76_layer_2_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 2 [])
      LColor.r LColor.p 24 cert76_seen_2_42_3 = cert76_component_2_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 2 []) LColor.r LColor.p
    cert76_seen_2_42_3 cert76_layer_2_42_3_eq 24

theorem cert76_step_2_42 :
    closedCollarIndexStepBool word fiber76 2 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_2_42)
    (by decide) (by decide)
    (by simpa [cert76_move_2_42] using cert76_component_2_42_eq)
    (by decide) (by decide) (by decide)

def cert76_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_1_0 = cert76_layer_3_1_0 := by
  decide

def cert76_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_3_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_1_1 = cert76_layer_3_1_1 := by
  decide

def cert76_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_3_1_2 : List ChainEdge :=
  []

theorem cert76_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_1_2 = cert76_layer_3_1_2 := by
  decide

theorem cert76_component_3_1_eq :
    closedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert76_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 27 cert76_seen_3_1_0 = cert76_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_1_0 cert76_layer_3_1_0 26 cert76_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 26 cert76_seen_3_1_1 = cert76_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_1_1 cert76_layer_3_1_1 25 cert76_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 25 cert76_seen_3_1_2 = cert76_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_1_2 cert76_layer_3_1_2_eq 25

theorem cert76_step_3_1 :
    closedCollarIndexStepBool word fiber76 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_3_1)
    (by decide) (by decide)
    (by simpa [cert76_move_3_1] using cert76_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_3_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_3_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_3_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_3_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_3_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.b LColor.p cert76_seen_3_11_0 = cert76_layer_3_11_0 := by
  decide

def cert76_seen_3_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_3_11_1 : List ChainEdge :=
  []

theorem cert76_layer_3_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.b LColor.p cert76_seen_3_11_1 = cert76_layer_3_11_1 := by
  decide

theorem cert76_component_3_11_eq :
    closedCollarComponent word (listGetD fiber76 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_3_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.b LColor.p 27 cert76_seen_3_11_0 = cert76_component_3_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.b LColor.p
    cert76_seen_3_11_0 cert76_layer_3_11_0 26 cert76_layer_3_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.b LColor.p 26 cert76_seen_3_11_1 = cert76_component_3_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 3 []) LColor.b LColor.p
    cert76_seen_3_11_1 cert76_layer_3_11_1_eq 26

theorem cert76_step_3_11 :
    closedCollarIndexStepBool word fiber76 3 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_3_11)
    (by decide) (by decide)
    (by simpa [cert76_move_3_11] using cert76_component_3_11_eq)
    (by decide) (by decide) (by decide)

def cert76_move_3_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_3_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_3_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_19_0 = cert76_layer_3_19_0 := by
  decide

def cert76_seen_3_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_3_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_3_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_19_1 = cert76_layer_3_19_1 := by
  decide

def cert76_seen_3_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_3_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_3_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_19_2 = cert76_layer_3_19_2 := by
  decide

def cert76_seen_3_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_3_19_3 : List ChainEdge :=
  []

theorem cert76_layer_3_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.b cert76_seen_3_19_3 = cert76_layer_3_19_3 := by
  decide

theorem cert76_component_3_19_eq :
    closedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_3_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 27 cert76_seen_3_19_0 = cert76_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_19_0 cert76_layer_3_19_0 26 cert76_layer_3_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 26 cert76_seen_3_19_1 = cert76_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_19_1 cert76_layer_3_19_1 25 cert76_layer_3_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 25 cert76_seen_3_19_2 = cert76_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_19_2 cert76_layer_3_19_2 24 cert76_layer_3_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.b 24 cert76_seen_3_19_3 = cert76_component_3_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 3 []) LColor.r LColor.b
    cert76_seen_3_19_3 cert76_layer_3_19_3_eq 24

theorem cert76_step_3_19 :
    closedCollarIndexStepBool word fiber76 3 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_3_19)
    (by decide) (by decide)
    (by simpa [cert76_move_3_19] using cert76_component_3_19_eq)
    (by decide) (by decide) (by decide)

def cert76_move_3_43 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_3_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_3_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_3_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_3_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_43_0 = cert76_layer_3_43_0 := by
  decide

def cert76_seen_3_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_3_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_3_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_43_1 = cert76_layer_3_43_1 := by
  decide

def cert76_seen_3_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_3_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_3_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_43_2 = cert76_layer_3_43_2 := by
  decide

def cert76_seen_3_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_3_43_3 : List ChainEdge :=
  []

theorem cert76_layer_3_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 3 [])
      LColor.r LColor.p cert76_seen_3_43_3 = cert76_layer_3_43_3 := by
  decide

theorem cert76_component_3_43_eq :
    closedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_3_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 27 cert76_seen_3_43_0 = cert76_component_3_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_43_0 cert76_layer_3_43_0 26 cert76_layer_3_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 26 cert76_seen_3_43_1 = cert76_component_3_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_43_1 cert76_layer_3_43_1 25 cert76_layer_3_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 25 cert76_seen_3_43_2 = cert76_component_3_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_43_2 cert76_layer_3_43_2 24 cert76_layer_3_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 3 [])
      LColor.r LColor.p 24 cert76_seen_3_43_3 = cert76_component_3_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 3 []) LColor.r LColor.p
    cert76_seen_3_43_3 cert76_layer_3_43_3_eq 24

theorem cert76_step_3_43 :
    closedCollarIndexStepBool word fiber76 3 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_3_43)
    (by decide) (by decide)
    (by simpa [cert76_move_3_43] using cert76_component_3_43_eq)
    (by decide) (by decide) (by decide)

def cert76_move_4_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_seen_4_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_4_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_2_0 = cert76_layer_4_2_0 := by
  decide

def cert76_seen_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_2_1 = cert76_layer_4_2_1 := by
  decide

def cert76_seen_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_4_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_2_2 = cert76_layer_4_2_2 := by
  decide

def cert76_seen_4_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_4_2_3 : List ChainEdge :=
  []

theorem cert76_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_2_3 = cert76_layer_4_2_3 := by
  decide

theorem cert76_component_4_2_eq :
    closedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 27 cert76_seen_4_2_0 = cert76_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_2_0 cert76_layer_4_2_0 26 cert76_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 26 cert76_seen_4_2_1 = cert76_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_2_1 cert76_layer_4_2_1 25 cert76_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 25 cert76_seen_4_2_2 = cert76_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_2_2 cert76_layer_4_2_2 24 cert76_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 24 cert76_seen_4_2_3 = cert76_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_2_3 cert76_layer_4_2_3_eq 24

theorem cert76_step_4_2 :
    closedCollarIndexStepBool word fiber76 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_4_2)
    (by decide) (by decide)
    (by simpa [cert76_move_4_2] using cert76_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_4_12 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_4_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_4_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_4_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_4_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.b LColor.p cert76_seen_4_12_0 = cert76_layer_4_12_0 := by
  decide

def cert76_seen_4_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_4_12_1 : List ChainEdge :=
  []

theorem cert76_layer_4_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.b LColor.p cert76_seen_4_12_1 = cert76_layer_4_12_1 := by
  decide

theorem cert76_component_4_12_eq :
    closedCollarComponent word (listGetD fiber76 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_4_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.b LColor.p 27 cert76_seen_4_12_0 = cert76_component_4_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.b LColor.p
    cert76_seen_4_12_0 cert76_layer_4_12_0 26 cert76_layer_4_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.b LColor.p 26 cert76_seen_4_12_1 = cert76_component_4_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 4 []) LColor.b LColor.p
    cert76_seen_4_12_1 cert76_layer_4_12_1_eq 26

theorem cert76_step_4_12 :
    closedCollarIndexStepBool word fiber76 4 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_4_12)
    (by decide) (by decide)
    (by simpa [cert76_move_4_12] using cert76_component_4_12_eq)
    (by decide) (by decide) (by decide)

def cert76_move_4_44 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_4_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_4_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_4_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_4_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_44_0 = cert76_layer_4_44_0 := by
  decide

def cert76_seen_4_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_4_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_4_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_44_1 = cert76_layer_4_44_1 := by
  decide

def cert76_seen_4_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_4_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_4_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_44_2 = cert76_layer_4_44_2 := by
  decide

def cert76_seen_4_44_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_4_44_3 : List ChainEdge :=
  []

theorem cert76_layer_4_44_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 4 [])
      LColor.r LColor.p cert76_seen_4_44_3 = cert76_layer_4_44_3 := by
  decide

theorem cert76_component_4_44_eq :
    closedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_4_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 27 cert76_seen_4_44_0 = cert76_component_4_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_44_0 cert76_layer_4_44_0 26 cert76_layer_4_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 26 cert76_seen_4_44_1 = cert76_component_4_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_44_1 cert76_layer_4_44_1 25 cert76_layer_4_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 25 cert76_seen_4_44_2 = cert76_component_4_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_44_2 cert76_layer_4_44_2 24 cert76_layer_4_44_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 4 [])
      LColor.r LColor.p 24 cert76_seen_4_44_3 = cert76_component_4_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 4 []) LColor.r LColor.p
    cert76_seen_4_44_3 cert76_layer_4_44_3_eq 24

theorem cert76_step_4_44 :
    closedCollarIndexStepBool word fiber76 4 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_4_44)
    (by decide) (by decide)
    (by simpa [cert76_move_4_44] using cert76_component_4_44_eq)
    (by decide) (by decide) (by decide)

def cert76_move_5_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_5_7 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_5_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_5_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_5_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.b LColor.p cert76_seen_5_7_0 = cert76_layer_5_7_0 := by
  decide

def cert76_seen_5_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_5_7_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_5_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.b LColor.p cert76_seen_5_7_1 = cert76_layer_5_7_1 := by
  decide

def cert76_seen_5_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_5_7_2 : List ChainEdge :=
  []

theorem cert76_layer_5_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.b LColor.p cert76_seen_5_7_2 = cert76_layer_5_7_2 := by
  decide

theorem cert76_component_5_7_eq :
    closedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert76_component_5_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 5 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p 27 cert76_seen_5_7_0 = cert76_component_5_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.b LColor.p
    cert76_seen_5_7_0 cert76_layer_5_7_0 26 cert76_layer_5_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p 26 cert76_seen_5_7_1 = cert76_component_5_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.b LColor.p
    cert76_seen_5_7_1 cert76_layer_5_7_1 25 cert76_layer_5_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p 25 cert76_seen_5_7_2 = cert76_component_5_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 5 []) LColor.b LColor.p
    cert76_seen_5_7_2 cert76_layer_5_7_2_eq 25

theorem cert76_step_5_7 :
    closedCollarIndexStepBool word fiber76 5 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_5_7)
    (by decide) (by decide)
    (by simpa [cert76_move_5_7] using cert76_component_5_7_eq)
    (by decide) (by decide) (by decide)

def cert76_move_5_13 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_5_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_5_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_5_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_5_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.b LColor.p cert76_seen_5_13_0 = cert76_layer_5_13_0 := by
  decide

def cert76_seen_5_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_5_13_1 : List ChainEdge :=
  []

theorem cert76_layer_5_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.b LColor.p cert76_seen_5_13_1 = cert76_layer_5_13_1 := by
  decide

theorem cert76_component_5_13_eq :
    closedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_5_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p 27 cert76_seen_5_13_0 = cert76_component_5_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.b LColor.p
    cert76_seen_5_13_0 cert76_layer_5_13_0 26 cert76_layer_5_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.b LColor.p 26 cert76_seen_5_13_1 = cert76_component_5_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 5 []) LColor.b LColor.p
    cert76_seen_5_13_1 cert76_layer_5_13_1_eq 26

theorem cert76_step_5_13 :
    closedCollarIndexStepBool word fiber76 5 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_5_13)
    (by decide) (by decide)
    (by simpa [cert76_move_5_13] using cert76_component_5_13_eq)
    (by decide) (by decide) (by decide)

def cert76_move_5_45 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_5_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_5_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_5_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_5_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.p cert76_seen_5_45_0 = cert76_layer_5_45_0 := by
  decide

def cert76_seen_5_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_5_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_5_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.p cert76_seen_5_45_1 = cert76_layer_5_45_1 := by
  decide

def cert76_seen_5_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_5_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_5_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.p cert76_seen_5_45_2 = cert76_layer_5_45_2 := by
  decide

def cert76_seen_5_45_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_5_45_3 : List ChainEdge :=
  []

theorem cert76_layer_5_45_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 5 [])
      LColor.r LColor.p cert76_seen_5_45_3 = cert76_layer_5_45_3 := by
  decide

theorem cert76_component_5_45_eq :
    closedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_5_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.p 27 cert76_seen_5_45_0 = cert76_component_5_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.p
    cert76_seen_5_45_0 cert76_layer_5_45_0 26 cert76_layer_5_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.p 26 cert76_seen_5_45_1 = cert76_component_5_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.p
    cert76_seen_5_45_1 cert76_layer_5_45_1 25 cert76_layer_5_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.p 25 cert76_seen_5_45_2 = cert76_component_5_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 5 []) LColor.r LColor.p
    cert76_seen_5_45_2 cert76_layer_5_45_2 24 cert76_layer_5_45_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 5 [])
      LColor.r LColor.p 24 cert76_seen_5_45_3 = cert76_component_5_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 5 []) LColor.r LColor.p
    cert76_seen_5_45_3 cert76_layer_5_45_3_eq 24

theorem cert76_step_5_45 :
    closedCollarIndexStepBool word fiber76 5 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_5_45)
    (by decide) (by decide)
    (by simpa [cert76_move_5_45] using cert76_component_5_45_eq)
    (by decide) (by decide) (by decide)

def cert76_move_6_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_6_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_6_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_6_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_1_0 = cert76_layer_6_1_0 := by
  decide

def cert76_seen_6_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_6_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_6_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_1_1 = cert76_layer_6_1_1 := by
  decide

def cert76_seen_6_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_6_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_6_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_1_2 = cert76_layer_6_1_2 := by
  decide

def cert76_seen_6_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_6_1_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_6_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_1_3 = cert76_layer_6_1_3 := by
  decide

def cert76_seen_6_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_6_1_4 : List ChainEdge :=
  []

theorem cert76_layer_6_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_1_4 = cert76_layer_6_1_4 := by
  decide

theorem cert76_component_6_1_eq :
    closedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_6_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 6 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 27 cert76_seen_6_1_0 = cert76_component_6_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_1_0 cert76_layer_6_1_0 26 cert76_layer_6_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 26 cert76_seen_6_1_1 = cert76_component_6_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_1_1 cert76_layer_6_1_1 25 cert76_layer_6_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 25 cert76_seen_6_1_2 = cert76_component_6_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_1_2 cert76_layer_6_1_2 24 cert76_layer_6_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 24 cert76_seen_6_1_3 = cert76_component_6_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_1_3 cert76_layer_6_1_3 23 cert76_layer_6_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 23 cert76_seen_6_1_4 = cert76_component_6_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_1_4 cert76_layer_6_1_4_eq 23

theorem cert76_step_6_1 :
    closedCollarIndexStepBool word fiber76 6 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_6_1)
    (by decide) (by decide)
    (by simpa [cert76_move_6_1] using cert76_component_6_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_6_14 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_6_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_6_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.b LColor.p cert76_seen_6_14_0 = cert76_layer_6_14_0 := by
  decide

def cert76_seen_6_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_6_14_1 : List ChainEdge :=
  []

theorem cert76_layer_6_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.b LColor.p cert76_seen_6_14_1 = cert76_layer_6_14_1 := by
  decide

theorem cert76_component_6_14_eq :
    closedCollarComponent word (listGetD fiber76 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_6_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.b LColor.p 27 cert76_seen_6_14_0 = cert76_component_6_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.b LColor.p
    cert76_seen_6_14_0 cert76_layer_6_14_0 26 cert76_layer_6_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.b LColor.p 26 cert76_seen_6_14_1 = cert76_component_6_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 6 []) LColor.b LColor.p
    cert76_seen_6_14_1 cert76_layer_6_14_1_eq 26

theorem cert76_step_6_14 :
    closedCollarIndexStepBool word fiber76 6 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_6_14)
    (by decide) (by decide)
    (by simpa [cert76_move_6_14] using cert76_component_6_14_eq)
    (by decide) (by decide) (by decide)

def cert76_move_6_46 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_6_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_6_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_6_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_6_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_46_0 = cert76_layer_6_46_0 := by
  decide

def cert76_seen_6_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_6_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_6_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_46_1 = cert76_layer_6_46_1 := by
  decide

def cert76_seen_6_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_6_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_6_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_46_2 = cert76_layer_6_46_2 := by
  decide

def cert76_seen_6_46_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_6_46_3 : List ChainEdge :=
  []

theorem cert76_layer_6_46_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 6 [])
      LColor.r LColor.p cert76_seen_6_46_3 = cert76_layer_6_46_3 := by
  decide

theorem cert76_component_6_46_eq :
    closedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_6_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 27 cert76_seen_6_46_0 = cert76_component_6_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_46_0 cert76_layer_6_46_0 26 cert76_layer_6_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 26 cert76_seen_6_46_1 = cert76_component_6_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_46_1 cert76_layer_6_46_1 25 cert76_layer_6_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 25 cert76_seen_6_46_2 = cert76_component_6_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_46_2 cert76_layer_6_46_2 24 cert76_layer_6_46_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 6 [])
      LColor.r LColor.p 24 cert76_seen_6_46_3 = cert76_component_6_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 6 []) LColor.r LColor.p
    cert76_seen_6_46_3 cert76_layer_6_46_3_eq 24

theorem cert76_step_6_46 :
    closedCollarIndexStepBool word fiber76 6 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_6_46)
    (by decide) (by decide)
    (by simpa [cert76_move_6_46] using cert76_component_6_46_eq)
    (by decide) (by decide) (by decide)

def cert76_move_7_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert76_component_7_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_7_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_7_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_7_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_0_0 = cert76_layer_7_0_0 := by
  decide

def cert76_seen_7_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_7_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_7_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_0_1 = cert76_layer_7_0_1 := by
  decide

def cert76_seen_7_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_7_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_7_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_0_2 = cert76_layer_7_0_2 := by
  decide

def cert76_seen_7_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_7_0_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_7_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_0_3 = cert76_layer_7_0_3 := by
  decide

def cert76_seen_7_0_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_7_0_4 : List ChainEdge :=
  []

theorem cert76_layer_7_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_0_4 = cert76_layer_7_0_4 := by
  decide

theorem cert76_component_7_0_eq :
    closedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert76_component_7_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 7 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 27 cert76_seen_7_0_0 = cert76_component_7_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_0_0 cert76_layer_7_0_0 26 cert76_layer_7_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 26 cert76_seen_7_0_1 = cert76_component_7_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_0_1 cert76_layer_7_0_1 25 cert76_layer_7_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 25 cert76_seen_7_0_2 = cert76_component_7_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_0_2 cert76_layer_7_0_2 24 cert76_layer_7_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 24 cert76_seen_7_0_3 = cert76_component_7_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_0_3 cert76_layer_7_0_3 23 cert76_layer_7_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 23 cert76_seen_7_0_4 = cert76_component_7_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_0_4 cert76_layer_7_0_4_eq 23

theorem cert76_step_7_0 :
    closedCollarIndexStepBool word fiber76 7 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_7_0)
    (by decide) (by decide)
    (by simpa [cert76_move_7_0] using cert76_component_7_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_7_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_7_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_7_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_7_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_7_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.b LColor.p cert76_seen_7_5_0 = cert76_layer_7_5_0 := by
  decide

def cert76_seen_7_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_7_5_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_7_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.b LColor.p cert76_seen_7_5_1 = cert76_layer_7_5_1 := by
  decide

def cert76_seen_7_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_7_5_2 : List ChainEdge :=
  []

theorem cert76_layer_7_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.b LColor.p cert76_seen_7_5_2 = cert76_layer_7_5_2 := by
  decide

theorem cert76_component_7_5_eq :
    closedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert76_component_7_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 7 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p 27 cert76_seen_7_5_0 = cert76_component_7_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.b LColor.p
    cert76_seen_7_5_0 cert76_layer_7_5_0 26 cert76_layer_7_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p 26 cert76_seen_7_5_1 = cert76_component_7_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.b LColor.p
    cert76_seen_7_5_1 cert76_layer_7_5_1 25 cert76_layer_7_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p 25 cert76_seen_7_5_2 = cert76_component_7_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 7 []) LColor.b LColor.p
    cert76_seen_7_5_2 cert76_layer_7_5_2_eq 25

theorem cert76_step_7_5 :
    closedCollarIndexStepBool word fiber76 7 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_7_5)
    (by decide) (by decide)
    (by simpa [cert76_move_7_5] using cert76_component_7_5_eq)
    (by decide) (by decide) (by decide)

def cert76_move_7_15 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_7_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_7_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.b LColor.p cert76_seen_7_15_0 = cert76_layer_7_15_0 := by
  decide

def cert76_seen_7_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_7_15_1 : List ChainEdge :=
  []

theorem cert76_layer_7_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.b LColor.p cert76_seen_7_15_1 = cert76_layer_7_15_1 := by
  decide

theorem cert76_component_7_15_eq :
    closedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_7_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p 27 cert76_seen_7_15_0 = cert76_component_7_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.b LColor.p
    cert76_seen_7_15_0 cert76_layer_7_15_0 26 cert76_layer_7_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.b LColor.p 26 cert76_seen_7_15_1 = cert76_component_7_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 7 []) LColor.b LColor.p
    cert76_seen_7_15_1 cert76_layer_7_15_1_eq 26

theorem cert76_step_7_15 :
    closedCollarIndexStepBool word fiber76 7 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_7_15)
    (by decide) (by decide)
    (by simpa [cert76_move_7_15] using cert76_component_7_15_eq)
    (by decide) (by decide) (by decide)

def cert76_move_7_47 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_7_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_7_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_7_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_7_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_47_0 = cert76_layer_7_47_0 := by
  decide

def cert76_seen_7_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_7_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_7_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_47_1 = cert76_layer_7_47_1 := by
  decide

def cert76_seen_7_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_7_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_7_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_47_2 = cert76_layer_7_47_2 := by
  decide

def cert76_seen_7_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_7_47_3 : List ChainEdge :=
  []

theorem cert76_layer_7_47_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 7 [])
      LColor.r LColor.p cert76_seen_7_47_3 = cert76_layer_7_47_3 := by
  decide

theorem cert76_component_7_47_eq :
    closedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_7_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 27 cert76_seen_7_47_0 = cert76_component_7_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_47_0 cert76_layer_7_47_0 26 cert76_layer_7_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 26 cert76_seen_7_47_1 = cert76_component_7_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_47_1 cert76_layer_7_47_1 25 cert76_layer_7_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 25 cert76_seen_7_47_2 = cert76_component_7_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_47_2 cert76_layer_7_47_2 24 cert76_layer_7_47_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 7 [])
      LColor.r LColor.p 24 cert76_seen_7_47_3 = cert76_component_7_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 7 []) LColor.r LColor.p
    cert76_seen_7_47_3 cert76_layer_7_47_3_eq 24

theorem cert76_step_7_47 :
    closedCollarIndexStepBool word fiber76 7 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_7_47)
    (by decide) (by decide)
    (by simpa [cert76_move_7_47] using cert76_component_7_47_eq)
    (by decide) (by decide) (by decide)

def cert76_move_8_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_8_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_8_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_8_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.b LColor.p cert76_seen_8_0_0 = cert76_layer_8_0_0 := by
  decide

def cert76_seen_8_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_8_0_1 : List ChainEdge :=
  []

theorem cert76_layer_8_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.b LColor.p cert76_seen_8_0_1 = cert76_layer_8_0_1 := by
  decide

theorem cert76_component_8_0_eq :
    closedCollarComponent word (listGetD fiber76 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_8_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.b LColor.p 27 cert76_seen_8_0_0 = cert76_component_8_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.b LColor.p
    cert76_seen_8_0_0 cert76_layer_8_0_0 26 cert76_layer_8_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.b LColor.p 26 cert76_seen_8_0_1 = cert76_component_8_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 8 []) LColor.b LColor.p
    cert76_seen_8_0_1 cert76_layer_8_0_1_eq 26

theorem cert76_step_8_0 :
    closedCollarIndexStepBool word fiber76 8 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_8_0)
    (by decide) (by decide)
    (by simpa [cert76_move_8_0] using cert76_component_8_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_8_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_8_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_8_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.b cert76_seen_8_20_0 = cert76_layer_8_20_0 := by
  decide

def cert76_seen_8_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_8_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_8_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.b cert76_seen_8_20_1 = cert76_layer_8_20_1 := by
  decide

def cert76_seen_8_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_8_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_8_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.b cert76_seen_8_20_2 = cert76_layer_8_20_2 := by
  decide

def cert76_seen_8_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_8_20_3 : List ChainEdge :=
  []

theorem cert76_layer_8_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.b cert76_seen_8_20_3 = cert76_layer_8_20_3 := by
  decide

theorem cert76_component_8_20_eq :
    closedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_8_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.b 27 cert76_seen_8_20_0 = cert76_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.b
    cert76_seen_8_20_0 cert76_layer_8_20_0 26 cert76_layer_8_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.b 26 cert76_seen_8_20_1 = cert76_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.b
    cert76_seen_8_20_1 cert76_layer_8_20_1 25 cert76_layer_8_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.b 25 cert76_seen_8_20_2 = cert76_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.b
    cert76_seen_8_20_2 cert76_layer_8_20_2 24 cert76_layer_8_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.b 24 cert76_seen_8_20_3 = cert76_component_8_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 8 []) LColor.r LColor.b
    cert76_seen_8_20_3 cert76_layer_8_20_3_eq 24

theorem cert76_step_8_20 :
    closedCollarIndexStepBool word fiber76 8 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_8_20)
    (by decide) (by decide)
    (by simpa [cert76_move_8_20] using cert76_component_8_20_eq)
    (by decide) (by decide) (by decide)

def cert76_move_8_32 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_8_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_8_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.p cert76_seen_8_32_0 = cert76_layer_8_32_0 := by
  decide

def cert76_seen_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_8_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.p cert76_seen_8_32_1 = cert76_layer_8_32_1 := by
  decide

def cert76_seen_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_8_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.p cert76_seen_8_32_2 = cert76_layer_8_32_2 := by
  decide

def cert76_seen_8_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_8_32_3 : List ChainEdge :=
  []

theorem cert76_layer_8_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 8 [])
      LColor.r LColor.p cert76_seen_8_32_3 = cert76_layer_8_32_3 := by
  decide

theorem cert76_component_8_32_eq :
    closedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_8_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.p 27 cert76_seen_8_32_0 = cert76_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.p
    cert76_seen_8_32_0 cert76_layer_8_32_0 26 cert76_layer_8_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.p 26 cert76_seen_8_32_1 = cert76_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.p
    cert76_seen_8_32_1 cert76_layer_8_32_1 25 cert76_layer_8_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.p 25 cert76_seen_8_32_2 = cert76_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 8 []) LColor.r LColor.p
    cert76_seen_8_32_2 cert76_layer_8_32_2 24 cert76_layer_8_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 8 [])
      LColor.r LColor.p 24 cert76_seen_8_32_3 = cert76_component_8_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 8 []) LColor.r LColor.p
    cert76_seen_8_32_3 cert76_layer_8_32_3_eq 24

theorem cert76_step_8_32 :
    closedCollarIndexStepBool word fiber76 8 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_8_32)
    (by decide) (by decide)
    (by simpa [cert76_move_8_32] using cert76_component_8_32_eq)
    (by decide) (by decide) (by decide)

def cert76_move_9_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_9_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_9_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_9_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.b LColor.p cert76_seen_9_1_0 = cert76_layer_9_1_0 := by
  decide

def cert76_seen_9_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_9_1_1 : List ChainEdge :=
  []

theorem cert76_layer_9_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.b LColor.p cert76_seen_9_1_1 = cert76_layer_9_1_1 := by
  decide

theorem cert76_component_9_1_eq :
    closedCollarComponent word (listGetD fiber76 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_9_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.b LColor.p 27 cert76_seen_9_1_0 = cert76_component_9_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.b LColor.p
    cert76_seen_9_1_0 cert76_layer_9_1_0 26 cert76_layer_9_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.b LColor.p 26 cert76_seen_9_1_1 = cert76_component_9_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 9 []) LColor.b LColor.p
    cert76_seen_9_1_1 cert76_layer_9_1_1_eq 26

theorem cert76_step_9_1 :
    closedCollarIndexStepBool word fiber76 9 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_9_1)
    (by decide) (by decide)
    (by simpa [cert76_move_9_1] using cert76_component_9_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_9_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_9_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_9_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.b cert76_seen_9_21_0 = cert76_layer_9_21_0 := by
  decide

def cert76_seen_9_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_9_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_9_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.b cert76_seen_9_21_1 = cert76_layer_9_21_1 := by
  decide

def cert76_seen_9_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_9_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_9_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.b cert76_seen_9_21_2 = cert76_layer_9_21_2 := by
  decide

def cert76_seen_9_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_9_21_3 : List ChainEdge :=
  []

theorem cert76_layer_9_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.b cert76_seen_9_21_3 = cert76_layer_9_21_3 := by
  decide

theorem cert76_component_9_21_eq :
    closedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_9_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.b 27 cert76_seen_9_21_0 = cert76_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.b
    cert76_seen_9_21_0 cert76_layer_9_21_0 26 cert76_layer_9_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.b 26 cert76_seen_9_21_1 = cert76_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.b
    cert76_seen_9_21_1 cert76_layer_9_21_1 25 cert76_layer_9_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.b 25 cert76_seen_9_21_2 = cert76_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.b
    cert76_seen_9_21_2 cert76_layer_9_21_2 24 cert76_layer_9_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.b 24 cert76_seen_9_21_3 = cert76_component_9_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 9 []) LColor.r LColor.b
    cert76_seen_9_21_3 cert76_layer_9_21_3_eq 24

theorem cert76_step_9_21 :
    closedCollarIndexStepBool word fiber76 9 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_9_21)
    (by decide) (by decide)
    (by simpa [cert76_move_9_21] using cert76_component_9_21_eq)
    (by decide) (by decide) (by decide)

def cert76_move_9_33 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_9_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_9_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.p cert76_seen_9_33_0 = cert76_layer_9_33_0 := by
  decide

def cert76_seen_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_9_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.p cert76_seen_9_33_1 = cert76_layer_9_33_1 := by
  decide

def cert76_seen_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_9_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.p cert76_seen_9_33_2 = cert76_layer_9_33_2 := by
  decide

def cert76_seen_9_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_9_33_3 : List ChainEdge :=
  []

theorem cert76_layer_9_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 9 [])
      LColor.r LColor.p cert76_seen_9_33_3 = cert76_layer_9_33_3 := by
  decide

theorem cert76_component_9_33_eq :
    closedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_9_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.p 27 cert76_seen_9_33_0 = cert76_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.p
    cert76_seen_9_33_0 cert76_layer_9_33_0 26 cert76_layer_9_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.p 26 cert76_seen_9_33_1 = cert76_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.p
    cert76_seen_9_33_1 cert76_layer_9_33_1 25 cert76_layer_9_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.p 25 cert76_seen_9_33_2 = cert76_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 9 []) LColor.r LColor.p
    cert76_seen_9_33_2 cert76_layer_9_33_2 24 cert76_layer_9_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 9 [])
      LColor.r LColor.p 24 cert76_seen_9_33_3 = cert76_component_9_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 9 []) LColor.r LColor.p
    cert76_seen_9_33_3 cert76_layer_9_33_3_eq 24

theorem cert76_step_9_33 :
    closedCollarIndexStepBool word fiber76 9 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_9_33)
    (by decide) (by decide)
    (by simpa [cert76_move_9_33] using cert76_component_9_33_eq)
    (by decide) (by decide) (by decide)

def cert76_move_10_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_10_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_10_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_10_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.b LColor.p cert76_seen_10_2_0 = cert76_layer_10_2_0 := by
  decide

def cert76_seen_10_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_10_2_1 : List ChainEdge :=
  []

theorem cert76_layer_10_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.b LColor.p cert76_seen_10_2_1 = cert76_layer_10_2_1 := by
  decide

theorem cert76_component_10_2_eq :
    closedCollarComponent word (listGetD fiber76 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_10_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.b LColor.p 27 cert76_seen_10_2_0 = cert76_component_10_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.b LColor.p
    cert76_seen_10_2_0 cert76_layer_10_2_0 26 cert76_layer_10_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.b LColor.p 26 cert76_seen_10_2_1 = cert76_component_10_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 10 []) LColor.b LColor.p
    cert76_seen_10_2_1 cert76_layer_10_2_1_eq 26

theorem cert76_step_10_2 :
    closedCollarIndexStepBool word fiber76 10 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_10_2)
    (by decide) (by decide)
    (by simpa [cert76_move_10_2] using cert76_component_10_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_10_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_10_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_10_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.b cert76_seen_10_22_0 = cert76_layer_10_22_0 := by
  decide

def cert76_seen_10_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_10_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_10_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.b cert76_seen_10_22_1 = cert76_layer_10_22_1 := by
  decide

def cert76_seen_10_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_10_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_10_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.b cert76_seen_10_22_2 = cert76_layer_10_22_2 := by
  decide

def cert76_seen_10_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_10_22_3 : List ChainEdge :=
  []

theorem cert76_layer_10_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.b cert76_seen_10_22_3 = cert76_layer_10_22_3 := by
  decide

theorem cert76_component_10_22_eq :
    closedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_10_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.b 27 cert76_seen_10_22_0 = cert76_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.b
    cert76_seen_10_22_0 cert76_layer_10_22_0 26 cert76_layer_10_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.b 26 cert76_seen_10_22_1 = cert76_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.b
    cert76_seen_10_22_1 cert76_layer_10_22_1 25 cert76_layer_10_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.b 25 cert76_seen_10_22_2 = cert76_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.b
    cert76_seen_10_22_2 cert76_layer_10_22_2 24 cert76_layer_10_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.b 24 cert76_seen_10_22_3 = cert76_component_10_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 10 []) LColor.r LColor.b
    cert76_seen_10_22_3 cert76_layer_10_22_3_eq 24

theorem cert76_step_10_22 :
    closedCollarIndexStepBool word fiber76 10 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_10_22)
    (by decide) (by decide)
    (by simpa [cert76_move_10_22] using cert76_component_10_22_eq)
    (by decide) (by decide) (by decide)

def cert76_move_10_34 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_10_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_10_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.p cert76_seen_10_34_0 = cert76_layer_10_34_0 := by
  decide

def cert76_seen_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_10_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.p cert76_seen_10_34_1 = cert76_layer_10_34_1 := by
  decide

def cert76_seen_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_10_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.p cert76_seen_10_34_2 = cert76_layer_10_34_2 := by
  decide

def cert76_seen_10_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_10_34_3 : List ChainEdge :=
  []

theorem cert76_layer_10_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 10 [])
      LColor.r LColor.p cert76_seen_10_34_3 = cert76_layer_10_34_3 := by
  decide

theorem cert76_component_10_34_eq :
    closedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_10_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.p 27 cert76_seen_10_34_0 = cert76_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.p
    cert76_seen_10_34_0 cert76_layer_10_34_0 26 cert76_layer_10_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.p 26 cert76_seen_10_34_1 = cert76_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.p
    cert76_seen_10_34_1 cert76_layer_10_34_1 25 cert76_layer_10_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.p 25 cert76_seen_10_34_2 = cert76_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 10 []) LColor.r LColor.p
    cert76_seen_10_34_2 cert76_layer_10_34_2 24 cert76_layer_10_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 10 [])
      LColor.r LColor.p 24 cert76_seen_10_34_3 = cert76_component_10_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 10 []) LColor.r LColor.p
    cert76_seen_10_34_3 cert76_layer_10_34_3_eq 24

theorem cert76_step_10_34 :
    closedCollarIndexStepBool word fiber76 10 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_10_34)
    (by decide) (by decide)
    (by simpa [cert76_move_10_34] using cert76_component_10_34_eq)
    (by decide) (by decide) (by decide)

def cert76_move_11_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_11_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_11_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_11_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.b LColor.p cert76_seen_11_3_0 = cert76_layer_11_3_0 := by
  decide

def cert76_seen_11_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_11_3_1 : List ChainEdge :=
  []

theorem cert76_layer_11_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.b LColor.p cert76_seen_11_3_1 = cert76_layer_11_3_1 := by
  decide

theorem cert76_component_11_3_eq :
    closedCollarComponent word (listGetD fiber76 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_11_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.b LColor.p 27 cert76_seen_11_3_0 = cert76_component_11_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.b LColor.p
    cert76_seen_11_3_0 cert76_layer_11_3_0 26 cert76_layer_11_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.b LColor.p 26 cert76_seen_11_3_1 = cert76_component_11_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 11 []) LColor.b LColor.p
    cert76_seen_11_3_1 cert76_layer_11_3_1_eq 26

theorem cert76_step_11_3 :
    closedCollarIndexStepBool word fiber76 11 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_11_3)
    (by decide) (by decide)
    (by simpa [cert76_move_11_3] using cert76_component_11_3_eq)
    (by decide) (by decide) (by decide)

def cert76_move_11_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_11_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_11_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.b cert76_seen_11_23_0 = cert76_layer_11_23_0 := by
  decide

def cert76_seen_11_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_11_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_11_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.b cert76_seen_11_23_1 = cert76_layer_11_23_1 := by
  decide

def cert76_seen_11_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_11_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_11_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.b cert76_seen_11_23_2 = cert76_layer_11_23_2 := by
  decide

def cert76_seen_11_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_11_23_3 : List ChainEdge :=
  []

theorem cert76_layer_11_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.b cert76_seen_11_23_3 = cert76_layer_11_23_3 := by
  decide

theorem cert76_component_11_23_eq :
    closedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_11_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.b 27 cert76_seen_11_23_0 = cert76_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.b
    cert76_seen_11_23_0 cert76_layer_11_23_0 26 cert76_layer_11_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.b 26 cert76_seen_11_23_1 = cert76_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.b
    cert76_seen_11_23_1 cert76_layer_11_23_1 25 cert76_layer_11_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.b 25 cert76_seen_11_23_2 = cert76_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.b
    cert76_seen_11_23_2 cert76_layer_11_23_2 24 cert76_layer_11_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.b 24 cert76_seen_11_23_3 = cert76_component_11_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 11 []) LColor.r LColor.b
    cert76_seen_11_23_3 cert76_layer_11_23_3_eq 24

theorem cert76_step_11_23 :
    closedCollarIndexStepBool word fiber76 11 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_11_23)
    (by decide) (by decide)
    (by simpa [cert76_move_11_23] using cert76_component_11_23_eq)
    (by decide) (by decide) (by decide)

def cert76_move_11_35 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_11_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_11_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.p cert76_seen_11_35_0 = cert76_layer_11_35_0 := by
  decide

def cert76_seen_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_11_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.p cert76_seen_11_35_1 = cert76_layer_11_35_1 := by
  decide

def cert76_seen_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_11_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.p cert76_seen_11_35_2 = cert76_layer_11_35_2 := by
  decide

def cert76_seen_11_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_11_35_3 : List ChainEdge :=
  []

theorem cert76_layer_11_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 11 [])
      LColor.r LColor.p cert76_seen_11_35_3 = cert76_layer_11_35_3 := by
  decide

theorem cert76_component_11_35_eq :
    closedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_11_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.p 27 cert76_seen_11_35_0 = cert76_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.p
    cert76_seen_11_35_0 cert76_layer_11_35_0 26 cert76_layer_11_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.p 26 cert76_seen_11_35_1 = cert76_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.p
    cert76_seen_11_35_1 cert76_layer_11_35_1 25 cert76_layer_11_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.p 25 cert76_seen_11_35_2 = cert76_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 11 []) LColor.r LColor.p
    cert76_seen_11_35_2 cert76_layer_11_35_2 24 cert76_layer_11_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 11 [])
      LColor.r LColor.p 24 cert76_seen_11_35_3 = cert76_component_11_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 11 []) LColor.r LColor.p
    cert76_seen_11_35_3 cert76_layer_11_35_3_eq 24

theorem cert76_step_11_35 :
    closedCollarIndexStepBool word fiber76 11 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_11_35)
    (by decide) (by decide)
    (by simpa [cert76_move_11_35] using cert76_component_11_35_eq)
    (by decide) (by decide) (by decide)

def cert76_move_12_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_12_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_12_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_12_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_12_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.b LColor.p cert76_seen_12_4_0 = cert76_layer_12_4_0 := by
  decide

def cert76_seen_12_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_12_4_1 : List ChainEdge :=
  []

theorem cert76_layer_12_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.b LColor.p cert76_seen_12_4_1 = cert76_layer_12_4_1 := by
  decide

theorem cert76_component_12_4_eq :
    closedCollarComponent word (listGetD fiber76 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_12_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.b LColor.p 27 cert76_seen_12_4_0 = cert76_component_12_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 12 []) LColor.b LColor.p
    cert76_seen_12_4_0 cert76_layer_12_4_0 26 cert76_layer_12_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.b LColor.p 26 cert76_seen_12_4_1 = cert76_component_12_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 12 []) LColor.b LColor.p
    cert76_seen_12_4_1 cert76_layer_12_4_1_eq 26

theorem cert76_step_12_4 :
    closedCollarIndexStepBool word fiber76 12 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_12_4)
    (by decide) (by decide)
    (by simpa [cert76_move_12_4] using cert76_component_12_4_eq)
    (by decide) (by decide) (by decide)

def cert76_move_12_36 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_12_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_12_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.r LColor.p cert76_seen_12_36_0 = cert76_layer_12_36_0 := by
  decide

def cert76_seen_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_12_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.r LColor.p cert76_seen_12_36_1 = cert76_layer_12_36_1 := by
  decide

def cert76_seen_12_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_12_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_12_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.r LColor.p cert76_seen_12_36_2 = cert76_layer_12_36_2 := by
  decide

def cert76_seen_12_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_12_36_3 : List ChainEdge :=
  []

theorem cert76_layer_12_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 12 [])
      LColor.r LColor.p cert76_seen_12_36_3 = cert76_layer_12_36_3 := by
  decide

theorem cert76_component_12_36_eq :
    closedCollarComponent word (listGetD fiber76 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_12_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.r LColor.p 27 cert76_seen_12_36_0 = cert76_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 12 []) LColor.r LColor.p
    cert76_seen_12_36_0 cert76_layer_12_36_0 26 cert76_layer_12_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.r LColor.p 26 cert76_seen_12_36_1 = cert76_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 12 []) LColor.r LColor.p
    cert76_seen_12_36_1 cert76_layer_12_36_1 25 cert76_layer_12_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.r LColor.p 25 cert76_seen_12_36_2 = cert76_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 12 []) LColor.r LColor.p
    cert76_seen_12_36_2 cert76_layer_12_36_2 24 cert76_layer_12_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 12 [])
      LColor.r LColor.p 24 cert76_seen_12_36_3 = cert76_component_12_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 12 []) LColor.r LColor.p
    cert76_seen_12_36_3 cert76_layer_12_36_3_eq 24

theorem cert76_step_12_36 :
    closedCollarIndexStepBool word fiber76 12 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_12_36)
    (by decide) (by decide)
    (by simpa [cert76_move_12_36] using cert76_component_12_36_eq)
    (by decide) (by decide) (by decide)

def cert76_move_13_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_13_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_13_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_13_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_13_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.b LColor.p cert76_seen_13_5_0 = cert76_layer_13_5_0 := by
  decide

def cert76_seen_13_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_13_5_1 : List ChainEdge :=
  []

theorem cert76_layer_13_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.b LColor.p cert76_seen_13_5_1 = cert76_layer_13_5_1 := by
  decide

theorem cert76_component_13_5_eq :
    closedCollarComponent word (listGetD fiber76 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_13_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.b LColor.p 27 cert76_seen_13_5_0 = cert76_component_13_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 13 []) LColor.b LColor.p
    cert76_seen_13_5_0 cert76_layer_13_5_0 26 cert76_layer_13_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.b LColor.p 26 cert76_seen_13_5_1 = cert76_component_13_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 13 []) LColor.b LColor.p
    cert76_seen_13_5_1 cert76_layer_13_5_1_eq 26

theorem cert76_step_13_5 :
    closedCollarIndexStepBool word fiber76 13 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_13_5)
    (by decide) (by decide)
    (by simpa [cert76_move_13_5] using cert76_component_13_5_eq)
    (by decide) (by decide) (by decide)

def cert76_move_13_37 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_13_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_13_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.r LColor.p cert76_seen_13_37_0 = cert76_layer_13_37_0 := by
  decide

def cert76_seen_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_13_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.r LColor.p cert76_seen_13_37_1 = cert76_layer_13_37_1 := by
  decide

def cert76_seen_13_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_13_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_13_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.r LColor.p cert76_seen_13_37_2 = cert76_layer_13_37_2 := by
  decide

def cert76_seen_13_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_13_37_3 : List ChainEdge :=
  []

theorem cert76_layer_13_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 13 [])
      LColor.r LColor.p cert76_seen_13_37_3 = cert76_layer_13_37_3 := by
  decide

theorem cert76_component_13_37_eq :
    closedCollarComponent word (listGetD fiber76 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_13_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.r LColor.p 27 cert76_seen_13_37_0 = cert76_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 13 []) LColor.r LColor.p
    cert76_seen_13_37_0 cert76_layer_13_37_0 26 cert76_layer_13_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.r LColor.p 26 cert76_seen_13_37_1 = cert76_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 13 []) LColor.r LColor.p
    cert76_seen_13_37_1 cert76_layer_13_37_1 25 cert76_layer_13_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.r LColor.p 25 cert76_seen_13_37_2 = cert76_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 13 []) LColor.r LColor.p
    cert76_seen_13_37_2 cert76_layer_13_37_2 24 cert76_layer_13_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 13 [])
      LColor.r LColor.p 24 cert76_seen_13_37_3 = cert76_component_13_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 13 []) LColor.r LColor.p
    cert76_seen_13_37_3 cert76_layer_13_37_3_eq 24

theorem cert76_step_13_37 :
    closedCollarIndexStepBool word fiber76 13 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_13_37)
    (by decide) (by decide)
    (by simpa [cert76_move_13_37] using cert76_component_13_37_eq)
    (by decide) (by decide) (by decide)

def cert76_move_14_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_14_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_14_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.b LColor.p cert76_seen_14_6_0 = cert76_layer_14_6_0 := by
  decide

def cert76_seen_14_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_14_6_1 : List ChainEdge :=
  []

theorem cert76_layer_14_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.b LColor.p cert76_seen_14_6_1 = cert76_layer_14_6_1 := by
  decide

theorem cert76_component_14_6_eq :
    closedCollarComponent word (listGetD fiber76 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_14_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.b LColor.p 27 cert76_seen_14_6_0 = cert76_component_14_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 14 []) LColor.b LColor.p
    cert76_seen_14_6_0 cert76_layer_14_6_0 26 cert76_layer_14_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.b LColor.p 26 cert76_seen_14_6_1 = cert76_component_14_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 14 []) LColor.b LColor.p
    cert76_seen_14_6_1 cert76_layer_14_6_1_eq 26

theorem cert76_step_14_6 :
    closedCollarIndexStepBool word fiber76 14 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_14_6)
    (by decide) (by decide)
    (by simpa [cert76_move_14_6] using cert76_component_14_6_eq)
    (by decide) (by decide) (by decide)

def cert76_move_14_38 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_14_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_14_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.r LColor.p cert76_seen_14_38_0 = cert76_layer_14_38_0 := by
  decide

def cert76_seen_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_14_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.r LColor.p cert76_seen_14_38_1 = cert76_layer_14_38_1 := by
  decide

def cert76_seen_14_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_14_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_14_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.r LColor.p cert76_seen_14_38_2 = cert76_layer_14_38_2 := by
  decide

def cert76_seen_14_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_14_38_3 : List ChainEdge :=
  []

theorem cert76_layer_14_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 14 [])
      LColor.r LColor.p cert76_seen_14_38_3 = cert76_layer_14_38_3 := by
  decide

theorem cert76_component_14_38_eq :
    closedCollarComponent word (listGetD fiber76 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_14_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.r LColor.p 27 cert76_seen_14_38_0 = cert76_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 14 []) LColor.r LColor.p
    cert76_seen_14_38_0 cert76_layer_14_38_0 26 cert76_layer_14_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.r LColor.p 26 cert76_seen_14_38_1 = cert76_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 14 []) LColor.r LColor.p
    cert76_seen_14_38_1 cert76_layer_14_38_1 25 cert76_layer_14_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.r LColor.p 25 cert76_seen_14_38_2 = cert76_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 14 []) LColor.r LColor.p
    cert76_seen_14_38_2 cert76_layer_14_38_2 24 cert76_layer_14_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 14 [])
      LColor.r LColor.p 24 cert76_seen_14_38_3 = cert76_component_14_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 14 []) LColor.r LColor.p
    cert76_seen_14_38_3 cert76_layer_14_38_3_eq 24

theorem cert76_step_14_38 :
    closedCollarIndexStepBool word fiber76 14 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_14_38)
    (by decide) (by decide)
    (by simpa [cert76_move_14_38] using cert76_component_14_38_eq)
    (by decide) (by decide) (by decide)

def cert76_move_15_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert76_component_15_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert76_layer_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_15_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.b LColor.p cert76_seen_15_7_0 = cert76_layer_15_7_0 := by
  decide

def cert76_seen_15_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_15_7_1 : List ChainEdge :=
  []

theorem cert76_layer_15_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.b LColor.p cert76_seen_15_7_1 = cert76_layer_15_7_1 := by
  decide

theorem cert76_component_15_7_eq :
    closedCollarComponent word (listGetD fiber76 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert76_component_15_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.b LColor.p 27 cert76_seen_15_7_0 = cert76_component_15_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 15 []) LColor.b LColor.p
    cert76_seen_15_7_0 cert76_layer_15_7_0 26 cert76_layer_15_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.b LColor.p 26 cert76_seen_15_7_1 = cert76_component_15_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 15 []) LColor.b LColor.p
    cert76_seen_15_7_1 cert76_layer_15_7_1_eq 26

theorem cert76_step_15_7 :
    closedCollarIndexStepBool word fiber76 15 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_15_7)
    (by decide) (by decide)
    (by simpa [cert76_move_15_7] using cert76_component_15_7_eq)
    (by decide) (by decide) (by decide)

def cert76_move_15_39 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_15_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_15_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.r LColor.p cert76_seen_15_39_0 = cert76_layer_15_39_0 := by
  decide

def cert76_seen_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_15_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.r LColor.p cert76_seen_15_39_1 = cert76_layer_15_39_1 := by
  decide

def cert76_seen_15_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_15_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_15_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.r LColor.p cert76_seen_15_39_2 = cert76_layer_15_39_2 := by
  decide

def cert76_seen_15_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_15_39_3 : List ChainEdge :=
  []

theorem cert76_layer_15_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 15 [])
      LColor.r LColor.p cert76_seen_15_39_3 = cert76_layer_15_39_3 := by
  decide

theorem cert76_component_15_39_eq :
    closedCollarComponent word (listGetD fiber76 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_15_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.r LColor.p 27 cert76_seen_15_39_0 = cert76_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 15 []) LColor.r LColor.p
    cert76_seen_15_39_0 cert76_layer_15_39_0 26 cert76_layer_15_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.r LColor.p 26 cert76_seen_15_39_1 = cert76_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 15 []) LColor.r LColor.p
    cert76_seen_15_39_1 cert76_layer_15_39_1 25 cert76_layer_15_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.r LColor.p 25 cert76_seen_15_39_2 = cert76_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 15 []) LColor.r LColor.p
    cert76_seen_15_39_2 cert76_layer_15_39_2 24 cert76_layer_15_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 15 [])
      LColor.r LColor.p 24 cert76_seen_15_39_3 = cert76_component_15_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 15 []) LColor.r LColor.p
    cert76_seen_15_39_3 cert76_layer_15_39_3_eq 24

theorem cert76_step_15_39 :
    closedCollarIndexStepBool word fiber76 15 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_15_39)
    (by decide) (by decide)
    (by simpa [cert76_move_15_39] using cert76_component_15_39_eq)
    (by decide) (by decide) (by decide)

def cert76_move_16_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_16_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.b cert76_seen_16_0_0 = cert76_layer_16_0_0 := by
  decide

def cert76_seen_16_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_16_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_16_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.b cert76_seen_16_0_1 = cert76_layer_16_0_1 := by
  decide

def cert76_seen_16_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_16_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_16_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.b cert76_seen_16_0_2 = cert76_layer_16_0_2 := by
  decide

def cert76_seen_16_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_16_0_3 : List ChainEdge :=
  []

theorem cert76_layer_16_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.b cert76_seen_16_0_3 = cert76_layer_16_0_3 := by
  decide

theorem cert76_component_16_0_eq :
    closedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_16_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.b 27 cert76_seen_16_0_0 = cert76_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.b
    cert76_seen_16_0_0 cert76_layer_16_0_0 26 cert76_layer_16_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.b 26 cert76_seen_16_0_1 = cert76_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.b
    cert76_seen_16_0_1 cert76_layer_16_0_1 25 cert76_layer_16_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.b 25 cert76_seen_16_0_2 = cert76_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.b
    cert76_seen_16_0_2 cert76_layer_16_0_2 24 cert76_layer_16_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.b 24 cert76_seen_16_0_3 = cert76_component_16_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 16 []) LColor.r LColor.b
    cert76_seen_16_0_3 cert76_layer_16_0_3_eq 24

theorem cert76_step_16_0 :
    closedCollarIndexStepBool word fiber76 16 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_16_0)
    (by decide) (by decide)
    (by simpa [cert76_move_16_0] using cert76_component_16_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_16_27 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_16_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_16_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_16_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_16_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_0 = cert76_layer_16_27_0 := by
  decide

def cert76_seen_16_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_16_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_16_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_1 = cert76_layer_16_27_1 := by
  decide

def cert76_seen_16_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_16_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_16_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_2 = cert76_layer_16_27_2 := by
  decide

def cert76_seen_16_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_16_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_16_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_3 = cert76_layer_16_27_3 := by
  decide

def cert76_seen_16_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_16_27_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_16_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_4 = cert76_layer_16_27_4 := by
  decide

def cert76_seen_16_27_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_16_27_5 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_16_27_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_5 = cert76_layer_16_27_5 := by
  decide

def cert76_seen_16_27_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_16_27_6 : List ChainEdge :=
  []

theorem cert76_layer_16_27_6_eq :
    closedCollarComponentLayer word (listGetD fiber76 16 [])
      LColor.r LColor.p cert76_seen_16_27_6 = cert76_layer_16_27_6 := by
  decide

theorem cert76_component_16_27_eq :
    closedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_16_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 27 cert76_seen_16_27_0 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_0 cert76_layer_16_27_0 26 cert76_layer_16_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 26 cert76_seen_16_27_1 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_1 cert76_layer_16_27_1 25 cert76_layer_16_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 25 cert76_seen_16_27_2 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_2 cert76_layer_16_27_2 24 cert76_layer_16_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 24 cert76_seen_16_27_3 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_3 cert76_layer_16_27_3 23 cert76_layer_16_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 23 cert76_seen_16_27_4 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_4 cert76_layer_16_27_4 22 cert76_layer_16_27_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 22 cert76_seen_16_27_5 = cert76_component_16_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_5 cert76_layer_16_27_5 21 cert76_layer_16_27_5_eq]
  change closeClosedCollarComponent word (listGetD fiber76 16 [])
      LColor.r LColor.p 21 cert76_seen_16_27_6 = cert76_component_16_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 16 []) LColor.r LColor.p
    cert76_seen_16_27_6 cert76_layer_16_27_6_eq 21

theorem cert76_step_16_27 :
    closedCollarIndexStepBool word fiber76 16 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_16_27)
    (by decide) (by decide)
    (by simpa [cert76_move_16_27] using cert76_component_16_27_eq)
    (by decide) (by decide) (by decide)

def cert76_move_17_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_17_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.b cert76_seen_17_1_0 = cert76_layer_17_1_0 := by
  decide

def cert76_seen_17_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_17_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_17_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.b cert76_seen_17_1_1 = cert76_layer_17_1_1 := by
  decide

def cert76_seen_17_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_17_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_17_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.b cert76_seen_17_1_2 = cert76_layer_17_1_2 := by
  decide

def cert76_seen_17_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_17_1_3 : List ChainEdge :=
  []

theorem cert76_layer_17_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.b cert76_seen_17_1_3 = cert76_layer_17_1_3 := by
  decide

theorem cert76_component_17_1_eq :
    closedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_17_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.b 27 cert76_seen_17_1_0 = cert76_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.b
    cert76_seen_17_1_0 cert76_layer_17_1_0 26 cert76_layer_17_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.b 26 cert76_seen_17_1_1 = cert76_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.b
    cert76_seen_17_1_1 cert76_layer_17_1_1 25 cert76_layer_17_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.b 25 cert76_seen_17_1_2 = cert76_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.b
    cert76_seen_17_1_2 cert76_layer_17_1_2 24 cert76_layer_17_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.b 24 cert76_seen_17_1_3 = cert76_component_17_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 17 []) LColor.r LColor.b
    cert76_seen_17_1_3 cert76_layer_17_1_3_eq 24

theorem cert76_step_17_1 :
    closedCollarIndexStepBool word fiber76 17 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_17_1)
    (by decide) (by decide)
    (by simpa [cert76_move_17_1] using cert76_component_17_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_17_26 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_17_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_17_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_17_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_17_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_0 = cert76_layer_17_26_0 := by
  decide

def cert76_seen_17_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_17_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_17_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_1 = cert76_layer_17_26_1 := by
  decide

def cert76_seen_17_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_17_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_17_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_2 = cert76_layer_17_26_2 := by
  decide

def cert76_seen_17_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_17_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_17_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_3 = cert76_layer_17_26_3 := by
  decide

def cert76_seen_17_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_17_26_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_17_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_4 = cert76_layer_17_26_4 := by
  decide

def cert76_seen_17_26_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_17_26_5 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_17_26_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_5 = cert76_layer_17_26_5 := by
  decide

def cert76_seen_17_26_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_17_26_6 : List ChainEdge :=
  []

theorem cert76_layer_17_26_6_eq :
    closedCollarComponentLayer word (listGetD fiber76 17 [])
      LColor.r LColor.p cert76_seen_17_26_6 = cert76_layer_17_26_6 := by
  decide

theorem cert76_component_17_26_eq :
    closedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_17_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 27 cert76_seen_17_26_0 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_0 cert76_layer_17_26_0 26 cert76_layer_17_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 26 cert76_seen_17_26_1 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_1 cert76_layer_17_26_1 25 cert76_layer_17_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 25 cert76_seen_17_26_2 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_2 cert76_layer_17_26_2 24 cert76_layer_17_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 24 cert76_seen_17_26_3 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_3 cert76_layer_17_26_3 23 cert76_layer_17_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 23 cert76_seen_17_26_4 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_4 cert76_layer_17_26_4 22 cert76_layer_17_26_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 22 cert76_seen_17_26_5 = cert76_component_17_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_5 cert76_layer_17_26_5 21 cert76_layer_17_26_5_eq]
  change closeClosedCollarComponent word (listGetD fiber76 17 [])
      LColor.r LColor.p 21 cert76_seen_17_26_6 = cert76_component_17_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 17 []) LColor.r LColor.p
    cert76_seen_17_26_6 cert76_layer_17_26_6_eq 21

theorem cert76_step_17_26 :
    closedCollarIndexStepBool word fiber76 17 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_17_26)
    (by decide) (by decide)
    (by simpa [cert76_move_17_26] using cert76_component_17_26_eq)
    (by decide) (by decide) (by decide)

def cert76_move_18_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_18_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.b cert76_seen_18_2_0 = cert76_layer_18_2_0 := by
  decide

def cert76_seen_18_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_18_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_18_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.b cert76_seen_18_2_1 = cert76_layer_18_2_1 := by
  decide

def cert76_seen_18_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_18_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_18_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.b cert76_seen_18_2_2 = cert76_layer_18_2_2 := by
  decide

def cert76_seen_18_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_18_2_3 : List ChainEdge :=
  []

theorem cert76_layer_18_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.b cert76_seen_18_2_3 = cert76_layer_18_2_3 := by
  decide

theorem cert76_component_18_2_eq :
    closedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_18_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.b 27 cert76_seen_18_2_0 = cert76_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.b
    cert76_seen_18_2_0 cert76_layer_18_2_0 26 cert76_layer_18_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.b 26 cert76_seen_18_2_1 = cert76_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.b
    cert76_seen_18_2_1 cert76_layer_18_2_1 25 cert76_layer_18_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.b 25 cert76_seen_18_2_2 = cert76_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.b
    cert76_seen_18_2_2 cert76_layer_18_2_2 24 cert76_layer_18_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.b 24 cert76_seen_18_2_3 = cert76_component_18_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 18 []) LColor.r LColor.b
    cert76_seen_18_2_3 cert76_layer_18_2_3_eq 24

theorem cert76_step_18_2 :
    closedCollarIndexStepBool word fiber76 18 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_18_2)
    (by decide) (by decide)
    (by simpa [cert76_move_18_2] using cert76_component_18_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_18_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_18_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_seen_18_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_18_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_18_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_0 = cert76_layer_18_24_0 := by
  decide

def cert76_seen_18_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_18_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_18_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_1 = cert76_layer_18_24_1 := by
  decide

def cert76_seen_18_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_18_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_18_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_2 = cert76_layer_18_24_2 := by
  decide

def cert76_seen_18_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_18_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_18_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_3 = cert76_layer_18_24_3 := by
  decide

def cert76_seen_18_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_18_24_4 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_18_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_4 = cert76_layer_18_24_4 := by
  decide

def cert76_seen_18_24_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_18_24_5 : List ChainEdge :=
  []

theorem cert76_layer_18_24_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 18 [])
      LColor.r LColor.p cert76_seen_18_24_5 = cert76_layer_18_24_5 := by
  decide

theorem cert76_component_18_24_eq :
    closedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_18_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 27 cert76_seen_18_24_0 = cert76_component_18_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_0 cert76_layer_18_24_0 26 cert76_layer_18_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 26 cert76_seen_18_24_1 = cert76_component_18_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_1 cert76_layer_18_24_1 25 cert76_layer_18_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 25 cert76_seen_18_24_2 = cert76_component_18_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_2 cert76_layer_18_24_2 24 cert76_layer_18_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 24 cert76_seen_18_24_3 = cert76_component_18_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_3 cert76_layer_18_24_3 23 cert76_layer_18_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 23 cert76_seen_18_24_4 = cert76_component_18_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_4 cert76_layer_18_24_4 22 cert76_layer_18_24_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 18 [])
      LColor.r LColor.p 22 cert76_seen_18_24_5 = cert76_component_18_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 18 []) LColor.r LColor.p
    cert76_seen_18_24_5 cert76_layer_18_24_5_eq 22

theorem cert76_step_18_24 :
    closedCollarIndexStepBool word fiber76 18 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_18_24)
    (by decide) (by decide)
    (by simpa [cert76_move_18_24] using cert76_component_18_24_eq)
    (by decide) (by decide) (by decide)

def cert76_move_19_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_19_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 19 [])
      LColor.r LColor.b cert76_seen_19_3_0 = cert76_layer_19_3_0 := by
  decide

def cert76_seen_19_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_19_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_19_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 19 [])
      LColor.r LColor.b cert76_seen_19_3_1 = cert76_layer_19_3_1 := by
  decide

def cert76_seen_19_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_19_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_19_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 19 [])
      LColor.r LColor.b cert76_seen_19_3_2 = cert76_layer_19_3_2 := by
  decide

def cert76_seen_19_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_19_3_3 : List ChainEdge :=
  []

theorem cert76_layer_19_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 19 [])
      LColor.r LColor.b cert76_seen_19_3_3 = cert76_layer_19_3_3 := by
  decide

theorem cert76_component_19_3_eq :
    closedCollarComponent word (listGetD fiber76 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_19_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 19 [])
      LColor.r LColor.b 27 cert76_seen_19_3_0 = cert76_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 19 []) LColor.r LColor.b
    cert76_seen_19_3_0 cert76_layer_19_3_0 26 cert76_layer_19_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 19 [])
      LColor.r LColor.b 26 cert76_seen_19_3_1 = cert76_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 19 []) LColor.r LColor.b
    cert76_seen_19_3_1 cert76_layer_19_3_1 25 cert76_layer_19_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 19 [])
      LColor.r LColor.b 25 cert76_seen_19_3_2 = cert76_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 19 []) LColor.r LColor.b
    cert76_seen_19_3_2 cert76_layer_19_3_2 24 cert76_layer_19_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 19 [])
      LColor.r LColor.b 24 cert76_seen_19_3_3 = cert76_component_19_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 19 []) LColor.r LColor.b
    cert76_seen_19_3_3 cert76_layer_19_3_3_eq 24

theorem cert76_step_19_3 :
    closedCollarIndexStepBool word fiber76 19 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_19_3)
    (by decide) (by decide)
    (by simpa [cert76_move_19_3] using cert76_component_19_3_eq)
    (by decide) (by decide) (by decide)

def cert76_move_20_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_20_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_20_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 20 [])
      LColor.r LColor.b cert76_seen_20_8_0 = cert76_layer_20_8_0 := by
  decide

def cert76_seen_20_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_20_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_20_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 20 [])
      LColor.r LColor.b cert76_seen_20_8_1 = cert76_layer_20_8_1 := by
  decide

def cert76_seen_20_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_20_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_20_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 20 [])
      LColor.r LColor.b cert76_seen_20_8_2 = cert76_layer_20_8_2 := by
  decide

def cert76_seen_20_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_20_8_3 : List ChainEdge :=
  []

theorem cert76_layer_20_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 20 [])
      LColor.r LColor.b cert76_seen_20_8_3 = cert76_layer_20_8_3 := by
  decide

theorem cert76_component_20_8_eq :
    closedCollarComponent word (listGetD fiber76 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_20_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 20 [])
      LColor.r LColor.b 27 cert76_seen_20_8_0 = cert76_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 20 []) LColor.r LColor.b
    cert76_seen_20_8_0 cert76_layer_20_8_0 26 cert76_layer_20_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 20 [])
      LColor.r LColor.b 26 cert76_seen_20_8_1 = cert76_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 20 []) LColor.r LColor.b
    cert76_seen_20_8_1 cert76_layer_20_8_1 25 cert76_layer_20_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 20 [])
      LColor.r LColor.b 25 cert76_seen_20_8_2 = cert76_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 20 []) LColor.r LColor.b
    cert76_seen_20_8_2 cert76_layer_20_8_2 24 cert76_layer_20_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 20 [])
      LColor.r LColor.b 24 cert76_seen_20_8_3 = cert76_component_20_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 20 []) LColor.r LColor.b
    cert76_seen_20_8_3 cert76_layer_20_8_3_eq 24

theorem cert76_step_20_8 :
    closedCollarIndexStepBool word fiber76 20 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_20_8)
    (by decide) (by decide)
    (by simpa [cert76_move_20_8] using cert76_component_20_8_eq)
    (by decide) (by decide) (by decide)

def cert76_move_21_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_21_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_21_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 21 [])
      LColor.r LColor.b cert76_seen_21_9_0 = cert76_layer_21_9_0 := by
  decide

def cert76_seen_21_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_21_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_21_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 21 [])
      LColor.r LColor.b cert76_seen_21_9_1 = cert76_layer_21_9_1 := by
  decide

def cert76_seen_21_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_21_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_21_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 21 [])
      LColor.r LColor.b cert76_seen_21_9_2 = cert76_layer_21_9_2 := by
  decide

def cert76_seen_21_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_21_9_3 : List ChainEdge :=
  []

theorem cert76_layer_21_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 21 [])
      LColor.r LColor.b cert76_seen_21_9_3 = cert76_layer_21_9_3 := by
  decide

theorem cert76_component_21_9_eq :
    closedCollarComponent word (listGetD fiber76 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_21_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 21 [])
      LColor.r LColor.b 27 cert76_seen_21_9_0 = cert76_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 21 []) LColor.r LColor.b
    cert76_seen_21_9_0 cert76_layer_21_9_0 26 cert76_layer_21_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 21 [])
      LColor.r LColor.b 26 cert76_seen_21_9_1 = cert76_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 21 []) LColor.r LColor.b
    cert76_seen_21_9_1 cert76_layer_21_9_1 25 cert76_layer_21_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 21 [])
      LColor.r LColor.b 25 cert76_seen_21_9_2 = cert76_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 21 []) LColor.r LColor.b
    cert76_seen_21_9_2 cert76_layer_21_9_2 24 cert76_layer_21_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 21 [])
      LColor.r LColor.b 24 cert76_seen_21_9_3 = cert76_component_21_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 21 []) LColor.r LColor.b
    cert76_seen_21_9_3 cert76_layer_21_9_3_eq 24

theorem cert76_step_21_9 :
    closedCollarIndexStepBool word fiber76 21 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_21_9)
    (by decide) (by decide)
    (by simpa [cert76_move_21_9] using cert76_component_21_9_eq)
    (by decide) (by decide) (by decide)

def cert76_move_22_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_22_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_22_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 22 [])
      LColor.r LColor.b cert76_seen_22_10_0 = cert76_layer_22_10_0 := by
  decide

def cert76_seen_22_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_22_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_22_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 22 [])
      LColor.r LColor.b cert76_seen_22_10_1 = cert76_layer_22_10_1 := by
  decide

def cert76_seen_22_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_22_10_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_22_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 22 [])
      LColor.r LColor.b cert76_seen_22_10_2 = cert76_layer_22_10_2 := by
  decide

def cert76_seen_22_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_22_10_3 : List ChainEdge :=
  []

theorem cert76_layer_22_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 22 [])
      LColor.r LColor.b cert76_seen_22_10_3 = cert76_layer_22_10_3 := by
  decide

theorem cert76_component_22_10_eq :
    closedCollarComponent word (listGetD fiber76 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_22_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 22 [])
      LColor.r LColor.b 27 cert76_seen_22_10_0 = cert76_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 22 []) LColor.r LColor.b
    cert76_seen_22_10_0 cert76_layer_22_10_0 26 cert76_layer_22_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 22 [])
      LColor.r LColor.b 26 cert76_seen_22_10_1 = cert76_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 22 []) LColor.r LColor.b
    cert76_seen_22_10_1 cert76_layer_22_10_1 25 cert76_layer_22_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 22 [])
      LColor.r LColor.b 25 cert76_seen_22_10_2 = cert76_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 22 []) LColor.r LColor.b
    cert76_seen_22_10_2 cert76_layer_22_10_2 24 cert76_layer_22_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 22 [])
      LColor.r LColor.b 24 cert76_seen_22_10_3 = cert76_component_22_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 22 []) LColor.r LColor.b
    cert76_seen_22_10_3 cert76_layer_22_10_3_eq 24

theorem cert76_step_22_10 :
    closedCollarIndexStepBool word fiber76 22 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_22_10)
    (by decide) (by decide)
    (by simpa [cert76_move_22_10] using cert76_component_22_10_eq)
    (by decide) (by decide) (by decide)

def cert76_move_23_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_23_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_23_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 23 [])
      LColor.r LColor.b cert76_seen_23_11_0 = cert76_layer_23_11_0 := by
  decide

def cert76_seen_23_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_23_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_23_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 23 [])
      LColor.r LColor.b cert76_seen_23_11_1 = cert76_layer_23_11_1 := by
  decide

def cert76_seen_23_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_23_11_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_23_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 23 [])
      LColor.r LColor.b cert76_seen_23_11_2 = cert76_layer_23_11_2 := by
  decide

def cert76_seen_23_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_23_11_3 : List ChainEdge :=
  []

theorem cert76_layer_23_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 23 [])
      LColor.r LColor.b cert76_seen_23_11_3 = cert76_layer_23_11_3 := by
  decide

theorem cert76_component_23_11_eq :
    closedCollarComponent word (listGetD fiber76 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert76_component_23_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 23 [])
      LColor.r LColor.b 27 cert76_seen_23_11_0 = cert76_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 23 []) LColor.r LColor.b
    cert76_seen_23_11_0 cert76_layer_23_11_0 26 cert76_layer_23_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 23 [])
      LColor.r LColor.b 26 cert76_seen_23_11_1 = cert76_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 23 []) LColor.r LColor.b
    cert76_seen_23_11_1 cert76_layer_23_11_1 25 cert76_layer_23_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 23 [])
      LColor.r LColor.b 25 cert76_seen_23_11_2 = cert76_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 23 []) LColor.r LColor.b
    cert76_seen_23_11_2 cert76_layer_23_11_2 24 cert76_layer_23_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 23 [])
      LColor.r LColor.b 24 cert76_seen_23_11_3 = cert76_component_23_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 23 []) LColor.r LColor.b
    cert76_seen_23_11_3 cert76_layer_23_11_3_eq 24

theorem cert76_step_23_11 :
    closedCollarIndexStepBool word fiber76 23 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_23_11)
    (by decide) (by decide)
    (by simpa [cert76_move_23_11] using cert76_component_23_11_eq)
    (by decide) (by decide) (by decide)

def cert76_move_24_18 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_24_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_seen_24_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_24_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_24_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_0 = cert76_layer_24_18_0 := by
  decide

def cert76_seen_24_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_24_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_24_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_1 = cert76_layer_24_18_1 := by
  decide

def cert76_seen_24_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_24_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_24_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_2 = cert76_layer_24_18_2 := by
  decide

def cert76_seen_24_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_24_18_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_24_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_3 = cert76_layer_24_18_3 := by
  decide

def cert76_seen_24_18_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_24_18_4 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_24_18_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_4 = cert76_layer_24_18_4 := by
  decide

def cert76_seen_24_18_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_24_18_5 : List ChainEdge :=
  []

theorem cert76_layer_24_18_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 24 [])
      LColor.r LColor.p cert76_seen_24_18_5 = cert76_layer_24_18_5 := by
  decide

theorem cert76_component_24_18_eq :
    closedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_24_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 27 cert76_seen_24_18_0 = cert76_component_24_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_0 cert76_layer_24_18_0 26 cert76_layer_24_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 26 cert76_seen_24_18_1 = cert76_component_24_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_1 cert76_layer_24_18_1 25 cert76_layer_24_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 25 cert76_seen_24_18_2 = cert76_component_24_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_2 cert76_layer_24_18_2 24 cert76_layer_24_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 24 cert76_seen_24_18_3 = cert76_component_24_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_3 cert76_layer_24_18_3 23 cert76_layer_24_18_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 23 cert76_seen_24_18_4 = cert76_component_24_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_4 cert76_layer_24_18_4 22 cert76_layer_24_18_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 24 [])
      LColor.r LColor.p 22 cert76_seen_24_18_5 = cert76_component_24_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 24 []) LColor.r LColor.p
    cert76_seen_24_18_5 cert76_layer_24_18_5_eq 22

theorem cert76_step_24_18 :
    closedCollarIndexStepBool word fiber76 24 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_24_18)
    (by decide) (by decide)
    (by simpa [cert76_move_24_18] using cert76_component_24_18_eq)
    (by decide) (by decide) (by decide)

def cert76_move_25_27 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_25_27 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_25_27_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_25_27_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_25_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 25 [])
      LColor.b LColor.p cert76_seen_25_27_0 = cert76_layer_25_27_0 := by
  decide

def cert76_seen_25_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_25_27_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_25_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 25 [])
      LColor.b LColor.p cert76_seen_25_27_1 = cert76_layer_25_27_1 := by
  decide

def cert76_seen_25_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_25_27_2 : List ChainEdge :=
  []

theorem cert76_layer_25_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 25 [])
      LColor.b LColor.p cert76_seen_25_27_2 = cert76_layer_25_27_2 := by
  decide

theorem cert76_component_25_27_eq :
    closedCollarComponent word (listGetD fiber76 25 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert76_component_25_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 25 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 25 [])
      LColor.b LColor.p 27 cert76_seen_25_27_0 = cert76_component_25_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 25 []) LColor.b LColor.p
    cert76_seen_25_27_0 cert76_layer_25_27_0 26 cert76_layer_25_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 25 [])
      LColor.b LColor.p 26 cert76_seen_25_27_1 = cert76_component_25_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 25 []) LColor.b LColor.p
    cert76_seen_25_27_1 cert76_layer_25_27_1 25 cert76_layer_25_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 25 [])
      LColor.b LColor.p 25 cert76_seen_25_27_2 = cert76_component_25_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 25 []) LColor.b LColor.p
    cert76_seen_25_27_2 cert76_layer_25_27_2_eq 25

theorem cert76_step_25_27 :
    closedCollarIndexStepBool word fiber76 25 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_25_27)
    (by decide) (by decide)
    (by simpa [cert76_move_25_27] using cert76_component_25_27_eq)
    (by decide) (by decide) (by decide)

def cert76_move_26_17 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_26_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_26_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_26_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_26_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_0 = cert76_layer_26_17_0 := by
  decide

def cert76_seen_26_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_26_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_26_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_1 = cert76_layer_26_17_1 := by
  decide

def cert76_seen_26_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_26_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_26_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_2 = cert76_layer_26_17_2 := by
  decide

def cert76_seen_26_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_26_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_26_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_3 = cert76_layer_26_17_3 := by
  decide

def cert76_seen_26_17_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_26_17_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_26_17_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_4 = cert76_layer_26_17_4 := by
  decide

def cert76_seen_26_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_26_17_5 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_26_17_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_5 = cert76_layer_26_17_5 := by
  decide

def cert76_seen_26_17_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_26_17_6 : List ChainEdge :=
  []

theorem cert76_layer_26_17_6_eq :
    closedCollarComponentLayer word (listGetD fiber76 26 [])
      LColor.r LColor.p cert76_seen_26_17_6 = cert76_layer_26_17_6 := by
  decide

theorem cert76_component_26_17_eq :
    closedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_26_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 27 cert76_seen_26_17_0 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_0 cert76_layer_26_17_0 26 cert76_layer_26_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 26 cert76_seen_26_17_1 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_1 cert76_layer_26_17_1 25 cert76_layer_26_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 25 cert76_seen_26_17_2 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_2 cert76_layer_26_17_2 24 cert76_layer_26_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 24 cert76_seen_26_17_3 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_3 cert76_layer_26_17_3 23 cert76_layer_26_17_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 23 cert76_seen_26_17_4 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_4 cert76_layer_26_17_4 22 cert76_layer_26_17_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 22 cert76_seen_26_17_5 = cert76_component_26_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_5 cert76_layer_26_17_5 21 cert76_layer_26_17_5_eq]
  change closeClosedCollarComponent word (listGetD fiber76 26 [])
      LColor.r LColor.p 21 cert76_seen_26_17_6 = cert76_component_26_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 26 []) LColor.r LColor.p
    cert76_seen_26_17_6 cert76_layer_26_17_6_eq 21

theorem cert76_step_26_17 :
    closedCollarIndexStepBool word fiber76 26 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_26_17)
    (by decide) (by decide)
    (by simpa [cert76_move_26_17] using cert76_component_26_17_eq)
    (by decide) (by decide) (by decide)

def cert76_move_27_16 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_27_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_27_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_27_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_27_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_0 = cert76_layer_27_16_0 := by
  decide

def cert76_seen_27_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_27_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_27_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_1 = cert76_layer_27_16_1 := by
  decide

def cert76_seen_27_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_27_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert76_layer_27_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_2 = cert76_layer_27_16_2 := by
  decide

def cert76_seen_27_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert76_layer_27_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert76_layer_27_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_3 = cert76_layer_27_16_3 := by
  decide

def cert76_seen_27_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert76_layer_27_16_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert76_layer_27_16_4_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_4 = cert76_layer_27_16_4 := by
  decide

def cert76_seen_27_16_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert76_layer_27_16_5 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_27_16_5_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_5 = cert76_layer_27_16_5 := by
  decide

def cert76_seen_27_16_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_27_16_6 : List ChainEdge :=
  []

theorem cert76_layer_27_16_6_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.r LColor.p cert76_seen_27_16_6 = cert76_layer_27_16_6 := by
  decide

theorem cert76_component_27_16_eq :
    closedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_27_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 27 cert76_seen_27_16_0 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_0 cert76_layer_27_16_0 26 cert76_layer_27_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 26 cert76_seen_27_16_1 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_1 cert76_layer_27_16_1 25 cert76_layer_27_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 25 cert76_seen_27_16_2 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_2 cert76_layer_27_16_2 24 cert76_layer_27_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 24 cert76_seen_27_16_3 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_3 cert76_layer_27_16_3 23 cert76_layer_27_16_3_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 23 cert76_seen_27_16_4 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_4 cert76_layer_27_16_4 22 cert76_layer_27_16_4_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 22 cert76_seen_27_16_5 = cert76_component_27_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_5 cert76_layer_27_16_5 21 cert76_layer_27_16_5_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.r LColor.p 21 cert76_seen_27_16_6 = cert76_component_27_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 27 []) LColor.r LColor.p
    cert76_seen_27_16_6 cert76_layer_27_16_6_eq 21

theorem cert76_step_27_16 :
    closedCollarIndexStepBool word fiber76 27 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_27_16)
    (by decide) (by decide)
    (by simpa [cert76_move_27_16] using cert76_component_27_16_eq)
    (by decide) (by decide) (by decide)

def cert76_move_27_25 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert76_component_27_25 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_seen_27_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert76_layer_27_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert76_layer_27_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.b LColor.p cert76_seen_27_25_0 = cert76_layer_27_25_0 := by
  decide

def cert76_seen_27_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert76_layer_27_25_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert76_layer_27_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.b LColor.p cert76_seen_27_25_1 = cert76_layer_27_25_1 := by
  decide

def cert76_seen_27_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert76_layer_27_25_2 : List ChainEdge :=
  []

theorem cert76_layer_27_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 27 [])
      LColor.b LColor.p cert76_seen_27_25_2 = cert76_layer_27_25_2 := by
  decide

theorem cert76_component_27_25_eq :
    closedCollarComponent word (listGetD fiber76 27 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert76_component_27_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 27 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.b LColor.p 27 cert76_seen_27_25_0 = cert76_component_27_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.b LColor.p
    cert76_seen_27_25_0 cert76_layer_27_25_0 26 cert76_layer_27_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.b LColor.p 26 cert76_seen_27_25_1 = cert76_component_27_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 27 []) LColor.b LColor.p
    cert76_seen_27_25_1 cert76_layer_27_25_1 25 cert76_layer_27_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 27 [])
      LColor.b LColor.p 25 cert76_seen_27_25_2 = cert76_component_27_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 27 []) LColor.b LColor.p
    cert76_seen_27_25_2 cert76_layer_27_25_2_eq 25

theorem cert76_step_27_25 :
    closedCollarIndexStepBool word fiber76 27 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_27_25)
    (by decide) (by decide)
    (by simpa [cert76_move_27_25] using cert76_component_27_25_eq)
    (by decide) (by decide) (by decide)

def cert76_move_28_44 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_28_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_28_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_28_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_28_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 28 [])
      LColor.b LColor.p cert76_seen_28_44_0 = cert76_layer_28_44_0 := by
  decide

def cert76_seen_28_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_28_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_28_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 28 [])
      LColor.b LColor.p cert76_seen_28_44_1 = cert76_layer_28_44_1 := by
  decide

def cert76_seen_28_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_28_44_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_28_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 28 [])
      LColor.b LColor.p cert76_seen_28_44_2 = cert76_layer_28_44_2 := by
  decide

def cert76_seen_28_44_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_28_44_3 : List ChainEdge :=
  []

theorem cert76_layer_28_44_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 28 [])
      LColor.b LColor.p cert76_seen_28_44_3 = cert76_layer_28_44_3 := by
  decide

theorem cert76_component_28_44_eq :
    closedCollarComponent word (listGetD fiber76 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_28_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 28 [])
      LColor.b LColor.p 27 cert76_seen_28_44_0 = cert76_component_28_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 28 []) LColor.b LColor.p
    cert76_seen_28_44_0 cert76_layer_28_44_0 26 cert76_layer_28_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 28 [])
      LColor.b LColor.p 26 cert76_seen_28_44_1 = cert76_component_28_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 28 []) LColor.b LColor.p
    cert76_seen_28_44_1 cert76_layer_28_44_1 25 cert76_layer_28_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 28 [])
      LColor.b LColor.p 25 cert76_seen_28_44_2 = cert76_component_28_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 28 []) LColor.b LColor.p
    cert76_seen_28_44_2 cert76_layer_28_44_2 24 cert76_layer_28_44_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 28 [])
      LColor.b LColor.p 24 cert76_seen_28_44_3 = cert76_component_28_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 28 []) LColor.b LColor.p
    cert76_seen_28_44_3 cert76_layer_28_44_3_eq 24

theorem cert76_step_28_44 :
    closedCollarIndexStepBool word fiber76 28 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_28_44)
    (by decide) (by decide)
    (by simpa [cert76_move_28_44] using cert76_component_28_44_eq)
    (by decide) (by decide) (by decide)

def cert76_move_29_45 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_29_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_29_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_29_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_29_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 29 [])
      LColor.b LColor.p cert76_seen_29_45_0 = cert76_layer_29_45_0 := by
  decide

def cert76_seen_29_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_29_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_29_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 29 [])
      LColor.b LColor.p cert76_seen_29_45_1 = cert76_layer_29_45_1 := by
  decide

def cert76_seen_29_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_29_45_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_29_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 29 [])
      LColor.b LColor.p cert76_seen_29_45_2 = cert76_layer_29_45_2 := by
  decide

def cert76_seen_29_45_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_29_45_3 : List ChainEdge :=
  []

theorem cert76_layer_29_45_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 29 [])
      LColor.b LColor.p cert76_seen_29_45_3 = cert76_layer_29_45_3 := by
  decide

theorem cert76_component_29_45_eq :
    closedCollarComponent word (listGetD fiber76 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_29_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 29 [])
      LColor.b LColor.p 27 cert76_seen_29_45_0 = cert76_component_29_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 29 []) LColor.b LColor.p
    cert76_seen_29_45_0 cert76_layer_29_45_0 26 cert76_layer_29_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 29 [])
      LColor.b LColor.p 26 cert76_seen_29_45_1 = cert76_component_29_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 29 []) LColor.b LColor.p
    cert76_seen_29_45_1 cert76_layer_29_45_1 25 cert76_layer_29_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 29 [])
      LColor.b LColor.p 25 cert76_seen_29_45_2 = cert76_component_29_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 29 []) LColor.b LColor.p
    cert76_seen_29_45_2 cert76_layer_29_45_2 24 cert76_layer_29_45_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 29 [])
      LColor.b LColor.p 24 cert76_seen_29_45_3 = cert76_component_29_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 29 []) LColor.b LColor.p
    cert76_seen_29_45_3 cert76_layer_29_45_3_eq 24

theorem cert76_step_29_45 :
    closedCollarIndexStepBool word fiber76 29 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_29_45)
    (by decide) (by decide)
    (by simpa [cert76_move_29_45] using cert76_component_29_45_eq)
    (by decide) (by decide) (by decide)

def cert76_move_30_46 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_30_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_30_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_30_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_30_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 30 [])
      LColor.b LColor.p cert76_seen_30_46_0 = cert76_layer_30_46_0 := by
  decide

def cert76_seen_30_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_30_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_30_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 30 [])
      LColor.b LColor.p cert76_seen_30_46_1 = cert76_layer_30_46_1 := by
  decide

def cert76_seen_30_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_30_46_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_30_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 30 [])
      LColor.b LColor.p cert76_seen_30_46_2 = cert76_layer_30_46_2 := by
  decide

def cert76_seen_30_46_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_30_46_3 : List ChainEdge :=
  []

theorem cert76_layer_30_46_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 30 [])
      LColor.b LColor.p cert76_seen_30_46_3 = cert76_layer_30_46_3 := by
  decide

theorem cert76_component_30_46_eq :
    closedCollarComponent word (listGetD fiber76 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_30_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 30 [])
      LColor.b LColor.p 27 cert76_seen_30_46_0 = cert76_component_30_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 30 []) LColor.b LColor.p
    cert76_seen_30_46_0 cert76_layer_30_46_0 26 cert76_layer_30_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 30 [])
      LColor.b LColor.p 26 cert76_seen_30_46_1 = cert76_component_30_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 30 []) LColor.b LColor.p
    cert76_seen_30_46_1 cert76_layer_30_46_1 25 cert76_layer_30_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 30 [])
      LColor.b LColor.p 25 cert76_seen_30_46_2 = cert76_component_30_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 30 []) LColor.b LColor.p
    cert76_seen_30_46_2 cert76_layer_30_46_2 24 cert76_layer_30_46_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 30 [])
      LColor.b LColor.p 24 cert76_seen_30_46_3 = cert76_component_30_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 30 []) LColor.b LColor.p
    cert76_seen_30_46_3 cert76_layer_30_46_3_eq 24

theorem cert76_step_30_46 :
    closedCollarIndexStepBool word fiber76 30 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_30_46)
    (by decide) (by decide)
    (by simpa [cert76_move_30_46] using cert76_component_30_46_eq)
    (by decide) (by decide) (by decide)

def cert76_move_31_47 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_31_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_31_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_31_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_31_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 31 [])
      LColor.b LColor.p cert76_seen_31_47_0 = cert76_layer_31_47_0 := by
  decide

def cert76_seen_31_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_31_47_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_31_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 31 [])
      LColor.b LColor.p cert76_seen_31_47_1 = cert76_layer_31_47_1 := by
  decide

def cert76_seen_31_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_31_47_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_31_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 31 [])
      LColor.b LColor.p cert76_seen_31_47_2 = cert76_layer_31_47_2 := by
  decide

def cert76_seen_31_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_31_47_3 : List ChainEdge :=
  []

theorem cert76_layer_31_47_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 31 [])
      LColor.b LColor.p cert76_seen_31_47_3 = cert76_layer_31_47_3 := by
  decide

theorem cert76_component_31_47_eq :
    closedCollarComponent word (listGetD fiber76 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_31_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 31 [])
      LColor.b LColor.p 27 cert76_seen_31_47_0 = cert76_component_31_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 31 []) LColor.b LColor.p
    cert76_seen_31_47_0 cert76_layer_31_47_0 26 cert76_layer_31_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 31 [])
      LColor.b LColor.p 26 cert76_seen_31_47_1 = cert76_component_31_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 31 []) LColor.b LColor.p
    cert76_seen_31_47_1 cert76_layer_31_47_1 25 cert76_layer_31_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 31 [])
      LColor.b LColor.p 25 cert76_seen_31_47_2 = cert76_component_31_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 31 []) LColor.b LColor.p
    cert76_seen_31_47_2 cert76_layer_31_47_2 24 cert76_layer_31_47_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 31 [])
      LColor.b LColor.p 24 cert76_seen_31_47_3 = cert76_component_31_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 31 []) LColor.b LColor.p
    cert76_seen_31_47_3 cert76_layer_31_47_3_eq 24

theorem cert76_step_31_47 :
    closedCollarIndexStepBool word fiber76 31 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_31_47)
    (by decide) (by decide)
    (by simpa [cert76_move_31_47] using cert76_component_31_47_eq)
    (by decide) (by decide) (by decide)

def cert76_move_32_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_32_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_32_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 32 [])
      LColor.r LColor.p cert76_seen_32_8_0 = cert76_layer_32_8_0 := by
  decide

def cert76_seen_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_32_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 32 [])
      LColor.r LColor.p cert76_seen_32_8_1 = cert76_layer_32_8_1 := by
  decide

def cert76_seen_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_32_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 32 [])
      LColor.r LColor.p cert76_seen_32_8_2 = cert76_layer_32_8_2 := by
  decide

def cert76_seen_32_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_32_8_3 : List ChainEdge :=
  []

theorem cert76_layer_32_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 32 [])
      LColor.r LColor.p cert76_seen_32_8_3 = cert76_layer_32_8_3 := by
  decide

theorem cert76_component_32_8_eq :
    closedCollarComponent word (listGetD fiber76 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_32_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 32 [])
      LColor.r LColor.p 27 cert76_seen_32_8_0 = cert76_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 32 []) LColor.r LColor.p
    cert76_seen_32_8_0 cert76_layer_32_8_0 26 cert76_layer_32_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 32 [])
      LColor.r LColor.p 26 cert76_seen_32_8_1 = cert76_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 32 []) LColor.r LColor.p
    cert76_seen_32_8_1 cert76_layer_32_8_1 25 cert76_layer_32_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 32 [])
      LColor.r LColor.p 25 cert76_seen_32_8_2 = cert76_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 32 []) LColor.r LColor.p
    cert76_seen_32_8_2 cert76_layer_32_8_2 24 cert76_layer_32_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 32 [])
      LColor.r LColor.p 24 cert76_seen_32_8_3 = cert76_component_32_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 32 []) LColor.r LColor.p
    cert76_seen_32_8_3 cert76_layer_32_8_3_eq 24

theorem cert76_step_32_8 :
    closedCollarIndexStepBool word fiber76 32 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_32_8)
    (by decide) (by decide)
    (by simpa [cert76_move_32_8] using cert76_component_32_8_eq)
    (by decide) (by decide) (by decide)

def cert76_move_33_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_33_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_33_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 33 [])
      LColor.r LColor.p cert76_seen_33_9_0 = cert76_layer_33_9_0 := by
  decide

def cert76_seen_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_33_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 33 [])
      LColor.r LColor.p cert76_seen_33_9_1 = cert76_layer_33_9_1 := by
  decide

def cert76_seen_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_33_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 33 [])
      LColor.r LColor.p cert76_seen_33_9_2 = cert76_layer_33_9_2 := by
  decide

def cert76_seen_33_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_33_9_3 : List ChainEdge :=
  []

theorem cert76_layer_33_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 33 [])
      LColor.r LColor.p cert76_seen_33_9_3 = cert76_layer_33_9_3 := by
  decide

theorem cert76_component_33_9_eq :
    closedCollarComponent word (listGetD fiber76 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_33_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 33 [])
      LColor.r LColor.p 27 cert76_seen_33_9_0 = cert76_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 33 []) LColor.r LColor.p
    cert76_seen_33_9_0 cert76_layer_33_9_0 26 cert76_layer_33_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 33 [])
      LColor.r LColor.p 26 cert76_seen_33_9_1 = cert76_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 33 []) LColor.r LColor.p
    cert76_seen_33_9_1 cert76_layer_33_9_1 25 cert76_layer_33_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 33 [])
      LColor.r LColor.p 25 cert76_seen_33_9_2 = cert76_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 33 []) LColor.r LColor.p
    cert76_seen_33_9_2 cert76_layer_33_9_2 24 cert76_layer_33_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 33 [])
      LColor.r LColor.p 24 cert76_seen_33_9_3 = cert76_component_33_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 33 []) LColor.r LColor.p
    cert76_seen_33_9_3 cert76_layer_33_9_3_eq 24

theorem cert76_step_33_9 :
    closedCollarIndexStepBool word fiber76 33 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_33_9)
    (by decide) (by decide)
    (by simpa [cert76_move_33_9] using cert76_component_33_9_eq)
    (by decide) (by decide) (by decide)

def cert76_move_34_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_34_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_34_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 34 [])
      LColor.r LColor.p cert76_seen_34_10_0 = cert76_layer_34_10_0 := by
  decide

def cert76_seen_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_34_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 34 [])
      LColor.r LColor.p cert76_seen_34_10_1 = cert76_layer_34_10_1 := by
  decide

def cert76_seen_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_34_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 34 [])
      LColor.r LColor.p cert76_seen_34_10_2 = cert76_layer_34_10_2 := by
  decide

def cert76_seen_34_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_34_10_3 : List ChainEdge :=
  []

theorem cert76_layer_34_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 34 [])
      LColor.r LColor.p cert76_seen_34_10_3 = cert76_layer_34_10_3 := by
  decide

theorem cert76_component_34_10_eq :
    closedCollarComponent word (listGetD fiber76 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_34_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 34 [])
      LColor.r LColor.p 27 cert76_seen_34_10_0 = cert76_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 34 []) LColor.r LColor.p
    cert76_seen_34_10_0 cert76_layer_34_10_0 26 cert76_layer_34_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 34 [])
      LColor.r LColor.p 26 cert76_seen_34_10_1 = cert76_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 34 []) LColor.r LColor.p
    cert76_seen_34_10_1 cert76_layer_34_10_1 25 cert76_layer_34_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 34 [])
      LColor.r LColor.p 25 cert76_seen_34_10_2 = cert76_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 34 []) LColor.r LColor.p
    cert76_seen_34_10_2 cert76_layer_34_10_2 24 cert76_layer_34_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 34 [])
      LColor.r LColor.p 24 cert76_seen_34_10_3 = cert76_component_34_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 34 []) LColor.r LColor.p
    cert76_seen_34_10_3 cert76_layer_34_10_3_eq 24

theorem cert76_step_34_10 :
    closedCollarIndexStepBool word fiber76 34 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_34_10)
    (by decide) (by decide)
    (by simpa [cert76_move_34_10] using cert76_component_34_10_eq)
    (by decide) (by decide) (by decide)

def cert76_move_35_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_35_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_35_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 35 [])
      LColor.r LColor.p cert76_seen_35_11_0 = cert76_layer_35_11_0 := by
  decide

def cert76_seen_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_35_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 35 [])
      LColor.r LColor.p cert76_seen_35_11_1 = cert76_layer_35_11_1 := by
  decide

def cert76_seen_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_35_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 35 [])
      LColor.r LColor.p cert76_seen_35_11_2 = cert76_layer_35_11_2 := by
  decide

def cert76_seen_35_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_35_11_3 : List ChainEdge :=
  []

theorem cert76_layer_35_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 35 [])
      LColor.r LColor.p cert76_seen_35_11_3 = cert76_layer_35_11_3 := by
  decide

theorem cert76_component_35_11_eq :
    closedCollarComponent word (listGetD fiber76 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_35_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 35 [])
      LColor.r LColor.p 27 cert76_seen_35_11_0 = cert76_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 35 []) LColor.r LColor.p
    cert76_seen_35_11_0 cert76_layer_35_11_0 26 cert76_layer_35_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 35 [])
      LColor.r LColor.p 26 cert76_seen_35_11_1 = cert76_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 35 []) LColor.r LColor.p
    cert76_seen_35_11_1 cert76_layer_35_11_1 25 cert76_layer_35_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 35 [])
      LColor.r LColor.p 25 cert76_seen_35_11_2 = cert76_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 35 []) LColor.r LColor.p
    cert76_seen_35_11_2 cert76_layer_35_11_2 24 cert76_layer_35_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 35 [])
      LColor.r LColor.p 24 cert76_seen_35_11_3 = cert76_component_35_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 35 []) LColor.r LColor.p
    cert76_seen_35_11_3 cert76_layer_35_11_3_eq 24

theorem cert76_step_35_11 :
    closedCollarIndexStepBool word fiber76 35 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_35_11)
    (by decide) (by decide)
    (by simpa [cert76_move_35_11] using cert76_component_35_11_eq)
    (by decide) (by decide) (by decide)

def cert76_move_36_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_36_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_36_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 36 [])
      LColor.r LColor.p cert76_seen_36_12_0 = cert76_layer_36_12_0 := by
  decide

def cert76_seen_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_36_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 36 [])
      LColor.r LColor.p cert76_seen_36_12_1 = cert76_layer_36_12_1 := by
  decide

def cert76_seen_36_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_36_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_36_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 36 [])
      LColor.r LColor.p cert76_seen_36_12_2 = cert76_layer_36_12_2 := by
  decide

def cert76_seen_36_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_36_12_3 : List ChainEdge :=
  []

theorem cert76_layer_36_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 36 [])
      LColor.r LColor.p cert76_seen_36_12_3 = cert76_layer_36_12_3 := by
  decide

theorem cert76_component_36_12_eq :
    closedCollarComponent word (listGetD fiber76 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_36_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 36 [])
      LColor.r LColor.p 27 cert76_seen_36_12_0 = cert76_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 36 []) LColor.r LColor.p
    cert76_seen_36_12_0 cert76_layer_36_12_0 26 cert76_layer_36_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 36 [])
      LColor.r LColor.p 26 cert76_seen_36_12_1 = cert76_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 36 []) LColor.r LColor.p
    cert76_seen_36_12_1 cert76_layer_36_12_1 25 cert76_layer_36_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 36 [])
      LColor.r LColor.p 25 cert76_seen_36_12_2 = cert76_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 36 []) LColor.r LColor.p
    cert76_seen_36_12_2 cert76_layer_36_12_2 24 cert76_layer_36_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 36 [])
      LColor.r LColor.p 24 cert76_seen_36_12_3 = cert76_component_36_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 36 []) LColor.r LColor.p
    cert76_seen_36_12_3 cert76_layer_36_12_3_eq 24

theorem cert76_step_36_12 :
    closedCollarIndexStepBool word fiber76 36 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_36_12)
    (by decide) (by decide)
    (by simpa [cert76_move_36_12] using cert76_component_36_12_eq)
    (by decide) (by decide) (by decide)

def cert76_move_37_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_37_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_37_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 37 [])
      LColor.r LColor.p cert76_seen_37_13_0 = cert76_layer_37_13_0 := by
  decide

def cert76_seen_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_37_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 37 [])
      LColor.r LColor.p cert76_seen_37_13_1 = cert76_layer_37_13_1 := by
  decide

def cert76_seen_37_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_37_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_37_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 37 [])
      LColor.r LColor.p cert76_seen_37_13_2 = cert76_layer_37_13_2 := by
  decide

def cert76_seen_37_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_37_13_3 : List ChainEdge :=
  []

theorem cert76_layer_37_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 37 [])
      LColor.r LColor.p cert76_seen_37_13_3 = cert76_layer_37_13_3 := by
  decide

theorem cert76_component_37_13_eq :
    closedCollarComponent word (listGetD fiber76 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_37_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 37 [])
      LColor.r LColor.p 27 cert76_seen_37_13_0 = cert76_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 37 []) LColor.r LColor.p
    cert76_seen_37_13_0 cert76_layer_37_13_0 26 cert76_layer_37_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 37 [])
      LColor.r LColor.p 26 cert76_seen_37_13_1 = cert76_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 37 []) LColor.r LColor.p
    cert76_seen_37_13_1 cert76_layer_37_13_1 25 cert76_layer_37_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 37 [])
      LColor.r LColor.p 25 cert76_seen_37_13_2 = cert76_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 37 []) LColor.r LColor.p
    cert76_seen_37_13_2 cert76_layer_37_13_2 24 cert76_layer_37_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 37 [])
      LColor.r LColor.p 24 cert76_seen_37_13_3 = cert76_component_37_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 37 []) LColor.r LColor.p
    cert76_seen_37_13_3 cert76_layer_37_13_3_eq 24

theorem cert76_step_37_13 :
    closedCollarIndexStepBool word fiber76 37 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_37_13)
    (by decide) (by decide)
    (by simpa [cert76_move_37_13] using cert76_component_37_13_eq)
    (by decide) (by decide) (by decide)

def cert76_move_38_14 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_38_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_38_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 38 [])
      LColor.r LColor.p cert76_seen_38_14_0 = cert76_layer_38_14_0 := by
  decide

def cert76_seen_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_38_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 38 [])
      LColor.r LColor.p cert76_seen_38_14_1 = cert76_layer_38_14_1 := by
  decide

def cert76_seen_38_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_38_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_38_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 38 [])
      LColor.r LColor.p cert76_seen_38_14_2 = cert76_layer_38_14_2 := by
  decide

def cert76_seen_38_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_38_14_3 : List ChainEdge :=
  []

theorem cert76_layer_38_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 38 [])
      LColor.r LColor.p cert76_seen_38_14_3 = cert76_layer_38_14_3 := by
  decide

theorem cert76_component_38_14_eq :
    closedCollarComponent word (listGetD fiber76 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_38_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 38 [])
      LColor.r LColor.p 27 cert76_seen_38_14_0 = cert76_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 38 []) LColor.r LColor.p
    cert76_seen_38_14_0 cert76_layer_38_14_0 26 cert76_layer_38_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 38 [])
      LColor.r LColor.p 26 cert76_seen_38_14_1 = cert76_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 38 []) LColor.r LColor.p
    cert76_seen_38_14_1 cert76_layer_38_14_1 25 cert76_layer_38_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 38 [])
      LColor.r LColor.p 25 cert76_seen_38_14_2 = cert76_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 38 []) LColor.r LColor.p
    cert76_seen_38_14_2 cert76_layer_38_14_2 24 cert76_layer_38_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 38 [])
      LColor.r LColor.p 24 cert76_seen_38_14_3 = cert76_component_38_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 38 []) LColor.r LColor.p
    cert76_seen_38_14_3 cert76_layer_38_14_3_eq 24

theorem cert76_step_38_14 :
    closedCollarIndexStepBool word fiber76 38 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_38_14)
    (by decide) (by decide)
    (by simpa [cert76_move_38_14] using cert76_component_38_14_eq)
    (by decide) (by decide) (by decide)

def cert76_move_39_15 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_39_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_seen_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_39_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 39 [])
      LColor.r LColor.p cert76_seen_39_15_0 = cert76_layer_39_15_0 := by
  decide

def cert76_seen_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_39_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 39 [])
      LColor.r LColor.p cert76_seen_39_15_1 = cert76_layer_39_15_1 := by
  decide

def cert76_seen_39_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_39_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert76_layer_39_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 39 [])
      LColor.r LColor.p cert76_seen_39_15_2 = cert76_layer_39_15_2 := by
  decide

def cert76_seen_39_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert76_layer_39_15_3 : List ChainEdge :=
  []

theorem cert76_layer_39_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 39 [])
      LColor.r LColor.p cert76_seen_39_15_3 = cert76_layer_39_15_3 := by
  decide

theorem cert76_component_39_15_eq :
    closedCollarComponent word (listGetD fiber76 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_39_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 39 [])
      LColor.r LColor.p 27 cert76_seen_39_15_0 = cert76_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 39 []) LColor.r LColor.p
    cert76_seen_39_15_0 cert76_layer_39_15_0 26 cert76_layer_39_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 39 [])
      LColor.r LColor.p 26 cert76_seen_39_15_1 = cert76_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 39 []) LColor.r LColor.p
    cert76_seen_39_15_1 cert76_layer_39_15_1 25 cert76_layer_39_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 39 [])
      LColor.r LColor.p 25 cert76_seen_39_15_2 = cert76_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 39 []) LColor.r LColor.p
    cert76_seen_39_15_2 cert76_layer_39_15_2 24 cert76_layer_39_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 39 [])
      LColor.r LColor.p 24 cert76_seen_39_15_3 = cert76_component_39_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 39 []) LColor.r LColor.p
    cert76_seen_39_15_3 cert76_layer_39_15_3_eq 24

theorem cert76_step_39_15 :
    closedCollarIndexStepBool word fiber76 39 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_39_15)
    (by decide) (by decide)
    (by simpa [cert76_move_39_15] using cert76_component_39_15_eq)
    (by decide) (by decide) (by decide)

def cert76_move_40_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_40_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_40_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_40_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 40 [])
      LColor.r LColor.p cert76_seen_40_0_0 = cert76_layer_40_0_0 := by
  decide

def cert76_seen_40_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_40_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_40_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 40 [])
      LColor.r LColor.p cert76_seen_40_0_1 = cert76_layer_40_0_1 := by
  decide

def cert76_seen_40_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_40_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_40_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 40 [])
      LColor.r LColor.p cert76_seen_40_0_2 = cert76_layer_40_0_2 := by
  decide

def cert76_seen_40_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_40_0_3 : List ChainEdge :=
  []

theorem cert76_layer_40_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 40 [])
      LColor.r LColor.p cert76_seen_40_0_3 = cert76_layer_40_0_3 := by
  decide

theorem cert76_component_40_0_eq :
    closedCollarComponent word (listGetD fiber76 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_40_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 40 [])
      LColor.r LColor.p 27 cert76_seen_40_0_0 = cert76_component_40_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 40 []) LColor.r LColor.p
    cert76_seen_40_0_0 cert76_layer_40_0_0 26 cert76_layer_40_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 40 [])
      LColor.r LColor.p 26 cert76_seen_40_0_1 = cert76_component_40_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 40 []) LColor.r LColor.p
    cert76_seen_40_0_1 cert76_layer_40_0_1 25 cert76_layer_40_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 40 [])
      LColor.r LColor.p 25 cert76_seen_40_0_2 = cert76_component_40_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 40 []) LColor.r LColor.p
    cert76_seen_40_0_2 cert76_layer_40_0_2 24 cert76_layer_40_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 40 [])
      LColor.r LColor.p 24 cert76_seen_40_0_3 = cert76_component_40_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 40 []) LColor.r LColor.p
    cert76_seen_40_0_3 cert76_layer_40_0_3_eq 24

theorem cert76_step_40_0 :
    closedCollarIndexStepBool word fiber76 40 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_40_0)
    (by decide) (by decide)
    (by simpa [cert76_move_40_0] using cert76_component_40_0_eq)
    (by decide) (by decide) (by decide)

def cert76_move_41_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_41_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_41_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_41_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 41 [])
      LColor.r LColor.p cert76_seen_41_1_0 = cert76_layer_41_1_0 := by
  decide

def cert76_seen_41_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_41_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_41_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 41 [])
      LColor.r LColor.p cert76_seen_41_1_1 = cert76_layer_41_1_1 := by
  decide

def cert76_seen_41_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_41_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_41_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 41 [])
      LColor.r LColor.p cert76_seen_41_1_2 = cert76_layer_41_1_2 := by
  decide

def cert76_seen_41_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_41_1_3 : List ChainEdge :=
  []

theorem cert76_layer_41_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 41 [])
      LColor.r LColor.p cert76_seen_41_1_3 = cert76_layer_41_1_3 := by
  decide

theorem cert76_component_41_1_eq :
    closedCollarComponent word (listGetD fiber76 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_41_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 41 [])
      LColor.r LColor.p 27 cert76_seen_41_1_0 = cert76_component_41_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 41 []) LColor.r LColor.p
    cert76_seen_41_1_0 cert76_layer_41_1_0 26 cert76_layer_41_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 41 [])
      LColor.r LColor.p 26 cert76_seen_41_1_1 = cert76_component_41_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 41 []) LColor.r LColor.p
    cert76_seen_41_1_1 cert76_layer_41_1_1 25 cert76_layer_41_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 41 [])
      LColor.r LColor.p 25 cert76_seen_41_1_2 = cert76_component_41_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 41 []) LColor.r LColor.p
    cert76_seen_41_1_2 cert76_layer_41_1_2 24 cert76_layer_41_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 41 [])
      LColor.r LColor.p 24 cert76_seen_41_1_3 = cert76_component_41_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 41 []) LColor.r LColor.p
    cert76_seen_41_1_3 cert76_layer_41_1_3_eq 24

theorem cert76_step_41_1 :
    closedCollarIndexStepBool word fiber76 41 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_41_1)
    (by decide) (by decide)
    (by simpa [cert76_move_41_1] using cert76_component_41_1_eq)
    (by decide) (by decide) (by decide)

def cert76_move_42_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_42_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_42_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_42_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 42 [])
      LColor.r LColor.p cert76_seen_42_2_0 = cert76_layer_42_2_0 := by
  decide

def cert76_seen_42_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_42_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_42_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 42 [])
      LColor.r LColor.p cert76_seen_42_2_1 = cert76_layer_42_2_1 := by
  decide

def cert76_seen_42_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_42_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_42_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 42 [])
      LColor.r LColor.p cert76_seen_42_2_2 = cert76_layer_42_2_2 := by
  decide

def cert76_seen_42_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_42_2_3 : List ChainEdge :=
  []

theorem cert76_layer_42_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 42 [])
      LColor.r LColor.p cert76_seen_42_2_3 = cert76_layer_42_2_3 := by
  decide

theorem cert76_component_42_2_eq :
    closedCollarComponent word (listGetD fiber76 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_42_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 42 [])
      LColor.r LColor.p 27 cert76_seen_42_2_0 = cert76_component_42_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 42 []) LColor.r LColor.p
    cert76_seen_42_2_0 cert76_layer_42_2_0 26 cert76_layer_42_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 42 [])
      LColor.r LColor.p 26 cert76_seen_42_2_1 = cert76_component_42_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 42 []) LColor.r LColor.p
    cert76_seen_42_2_1 cert76_layer_42_2_1 25 cert76_layer_42_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 42 [])
      LColor.r LColor.p 25 cert76_seen_42_2_2 = cert76_component_42_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 42 []) LColor.r LColor.p
    cert76_seen_42_2_2 cert76_layer_42_2_2 24 cert76_layer_42_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 42 [])
      LColor.r LColor.p 24 cert76_seen_42_2_3 = cert76_component_42_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 42 []) LColor.r LColor.p
    cert76_seen_42_2_3 cert76_layer_42_2_3_eq 24

theorem cert76_step_42_2 :
    closedCollarIndexStepBool word fiber76 42 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_42_2)
    (by decide) (by decide)
    (by simpa [cert76_move_42_2] using cert76_component_42_2_eq)
    (by decide) (by decide) (by decide)

def cert76_move_43_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_43_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_43_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_43_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 43 [])
      LColor.r LColor.p cert76_seen_43_3_0 = cert76_layer_43_3_0 := by
  decide

def cert76_seen_43_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_43_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_43_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 43 [])
      LColor.r LColor.p cert76_seen_43_3_1 = cert76_layer_43_3_1 := by
  decide

def cert76_seen_43_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_43_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_43_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 43 [])
      LColor.r LColor.p cert76_seen_43_3_2 = cert76_layer_43_3_2 := by
  decide

def cert76_seen_43_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_43_3_3 : List ChainEdge :=
  []

theorem cert76_layer_43_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 43 [])
      LColor.r LColor.p cert76_seen_43_3_3 = cert76_layer_43_3_3 := by
  decide

theorem cert76_component_43_3_eq :
    closedCollarComponent word (listGetD fiber76 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_43_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 43 [])
      LColor.r LColor.p 27 cert76_seen_43_3_0 = cert76_component_43_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 43 []) LColor.r LColor.p
    cert76_seen_43_3_0 cert76_layer_43_3_0 26 cert76_layer_43_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 43 [])
      LColor.r LColor.p 26 cert76_seen_43_3_1 = cert76_component_43_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 43 []) LColor.r LColor.p
    cert76_seen_43_3_1 cert76_layer_43_3_1 25 cert76_layer_43_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 43 [])
      LColor.r LColor.p 25 cert76_seen_43_3_2 = cert76_component_43_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 43 []) LColor.r LColor.p
    cert76_seen_43_3_2 cert76_layer_43_3_2 24 cert76_layer_43_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 43 [])
      LColor.r LColor.p 24 cert76_seen_43_3_3 = cert76_component_43_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 43 []) LColor.r LColor.p
    cert76_seen_43_3_3 cert76_layer_43_3_3_eq 24

theorem cert76_step_43_3 :
    closedCollarIndexStepBool word fiber76 43 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_43_3)
    (by decide) (by decide)
    (by simpa [cert76_move_43_3] using cert76_component_43_3_eq)
    (by decide) (by decide) (by decide)

def cert76_move_44_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_44_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_44_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_44_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_44_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.r LColor.p cert76_seen_44_4_0 = cert76_layer_44_4_0 := by
  decide

def cert76_seen_44_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_44_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_44_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.r LColor.p cert76_seen_44_4_1 = cert76_layer_44_4_1 := by
  decide

def cert76_seen_44_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_44_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_44_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.r LColor.p cert76_seen_44_4_2 = cert76_layer_44_4_2 := by
  decide

def cert76_seen_44_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_44_4_3 : List ChainEdge :=
  []

theorem cert76_layer_44_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.r LColor.p cert76_seen_44_4_3 = cert76_layer_44_4_3 := by
  decide

theorem cert76_component_44_4_eq :
    closedCollarComponent word (listGetD fiber76 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_44_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.r LColor.p 27 cert76_seen_44_4_0 = cert76_component_44_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.r LColor.p
    cert76_seen_44_4_0 cert76_layer_44_4_0 26 cert76_layer_44_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.r LColor.p 26 cert76_seen_44_4_1 = cert76_component_44_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.r LColor.p
    cert76_seen_44_4_1 cert76_layer_44_4_1 25 cert76_layer_44_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.r LColor.p 25 cert76_seen_44_4_2 = cert76_component_44_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.r LColor.p
    cert76_seen_44_4_2 cert76_layer_44_4_2 24 cert76_layer_44_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.r LColor.p 24 cert76_seen_44_4_3 = cert76_component_44_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 44 []) LColor.r LColor.p
    cert76_seen_44_4_3 cert76_layer_44_4_3_eq 24

theorem cert76_step_44_4 :
    closedCollarIndexStepBool word fiber76 44 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_44_4)
    (by decide) (by decide)
    (by simpa [cert76_move_44_4] using cert76_component_44_4_eq)
    (by decide) (by decide) (by decide)

def cert76_move_44_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_44_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_44_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_44_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_44_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.b LColor.p cert76_seen_44_28_0 = cert76_layer_44_28_0 := by
  decide

def cert76_seen_44_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_44_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_44_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.b LColor.p cert76_seen_44_28_1 = cert76_layer_44_28_1 := by
  decide

def cert76_seen_44_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_44_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_44_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.b LColor.p cert76_seen_44_28_2 = cert76_layer_44_28_2 := by
  decide

def cert76_seen_44_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_44_28_3 : List ChainEdge :=
  []

theorem cert76_layer_44_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 44 [])
      LColor.b LColor.p cert76_seen_44_28_3 = cert76_layer_44_28_3 := by
  decide

theorem cert76_component_44_28_eq :
    closedCollarComponent word (listGetD fiber76 44 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_44_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 44 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.b LColor.p 27 cert76_seen_44_28_0 = cert76_component_44_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.b LColor.p
    cert76_seen_44_28_0 cert76_layer_44_28_0 26 cert76_layer_44_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.b LColor.p 26 cert76_seen_44_28_1 = cert76_component_44_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.b LColor.p
    cert76_seen_44_28_1 cert76_layer_44_28_1 25 cert76_layer_44_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.b LColor.p 25 cert76_seen_44_28_2 = cert76_component_44_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 44 []) LColor.b LColor.p
    cert76_seen_44_28_2 cert76_layer_44_28_2 24 cert76_layer_44_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 44 [])
      LColor.b LColor.p 24 cert76_seen_44_28_3 = cert76_component_44_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 44 []) LColor.b LColor.p
    cert76_seen_44_28_3 cert76_layer_44_28_3_eq 24

theorem cert76_step_44_28 :
    closedCollarIndexStepBool word fiber76 44 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_44_28)
    (by decide) (by decide)
    (by simpa [cert76_move_44_28] using cert76_component_44_28_eq)
    (by decide) (by decide) (by decide)

def cert76_move_45_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_45_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_45_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_45_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_45_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.r LColor.p cert76_seen_45_5_0 = cert76_layer_45_5_0 := by
  decide

def cert76_seen_45_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_45_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_45_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.r LColor.p cert76_seen_45_5_1 = cert76_layer_45_5_1 := by
  decide

def cert76_seen_45_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_45_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_45_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.r LColor.p cert76_seen_45_5_2 = cert76_layer_45_5_2 := by
  decide

def cert76_seen_45_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_45_5_3 : List ChainEdge :=
  []

theorem cert76_layer_45_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.r LColor.p cert76_seen_45_5_3 = cert76_layer_45_5_3 := by
  decide

theorem cert76_component_45_5_eq :
    closedCollarComponent word (listGetD fiber76 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_45_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.r LColor.p 27 cert76_seen_45_5_0 = cert76_component_45_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.r LColor.p
    cert76_seen_45_5_0 cert76_layer_45_5_0 26 cert76_layer_45_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.r LColor.p 26 cert76_seen_45_5_1 = cert76_component_45_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.r LColor.p
    cert76_seen_45_5_1 cert76_layer_45_5_1 25 cert76_layer_45_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.r LColor.p 25 cert76_seen_45_5_2 = cert76_component_45_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.r LColor.p
    cert76_seen_45_5_2 cert76_layer_45_5_2 24 cert76_layer_45_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.r LColor.p 24 cert76_seen_45_5_3 = cert76_component_45_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 45 []) LColor.r LColor.p
    cert76_seen_45_5_3 cert76_layer_45_5_3_eq 24

theorem cert76_step_45_5 :
    closedCollarIndexStepBool word fiber76 45 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_45_5)
    (by decide) (by decide)
    (by simpa [cert76_move_45_5] using cert76_component_45_5_eq)
    (by decide) (by decide) (by decide)

def cert76_move_45_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_45_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_45_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_45_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_45_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.b LColor.p cert76_seen_45_29_0 = cert76_layer_45_29_0 := by
  decide

def cert76_seen_45_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_45_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_45_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.b LColor.p cert76_seen_45_29_1 = cert76_layer_45_29_1 := by
  decide

def cert76_seen_45_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_45_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_45_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.b LColor.p cert76_seen_45_29_2 = cert76_layer_45_29_2 := by
  decide

def cert76_seen_45_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_45_29_3 : List ChainEdge :=
  []

theorem cert76_layer_45_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 45 [])
      LColor.b LColor.p cert76_seen_45_29_3 = cert76_layer_45_29_3 := by
  decide

theorem cert76_component_45_29_eq :
    closedCollarComponent word (listGetD fiber76 45 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_45_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 45 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.b LColor.p 27 cert76_seen_45_29_0 = cert76_component_45_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.b LColor.p
    cert76_seen_45_29_0 cert76_layer_45_29_0 26 cert76_layer_45_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.b LColor.p 26 cert76_seen_45_29_1 = cert76_component_45_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.b LColor.p
    cert76_seen_45_29_1 cert76_layer_45_29_1 25 cert76_layer_45_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.b LColor.p 25 cert76_seen_45_29_2 = cert76_component_45_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 45 []) LColor.b LColor.p
    cert76_seen_45_29_2 cert76_layer_45_29_2 24 cert76_layer_45_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 45 [])
      LColor.b LColor.p 24 cert76_seen_45_29_3 = cert76_component_45_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 45 []) LColor.b LColor.p
    cert76_seen_45_29_3 cert76_layer_45_29_3_eq 24

theorem cert76_step_45_29 :
    closedCollarIndexStepBool word fiber76 45 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_45_29)
    (by decide) (by decide)
    (by simpa [cert76_move_45_29] using cert76_component_45_29_eq)
    (by decide) (by decide) (by decide)

def cert76_move_46_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_46_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_46_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_46_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_46_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.r LColor.p cert76_seen_46_6_0 = cert76_layer_46_6_0 := by
  decide

def cert76_seen_46_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_46_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_46_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.r LColor.p cert76_seen_46_6_1 = cert76_layer_46_6_1 := by
  decide

def cert76_seen_46_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_46_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_46_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.r LColor.p cert76_seen_46_6_2 = cert76_layer_46_6_2 := by
  decide

def cert76_seen_46_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_46_6_3 : List ChainEdge :=
  []

theorem cert76_layer_46_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.r LColor.p cert76_seen_46_6_3 = cert76_layer_46_6_3 := by
  decide

theorem cert76_component_46_6_eq :
    closedCollarComponent word (listGetD fiber76 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_46_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.r LColor.p 27 cert76_seen_46_6_0 = cert76_component_46_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.r LColor.p
    cert76_seen_46_6_0 cert76_layer_46_6_0 26 cert76_layer_46_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.r LColor.p 26 cert76_seen_46_6_1 = cert76_component_46_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.r LColor.p
    cert76_seen_46_6_1 cert76_layer_46_6_1 25 cert76_layer_46_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.r LColor.p 25 cert76_seen_46_6_2 = cert76_component_46_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.r LColor.p
    cert76_seen_46_6_2 cert76_layer_46_6_2 24 cert76_layer_46_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.r LColor.p 24 cert76_seen_46_6_3 = cert76_component_46_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 46 []) LColor.r LColor.p
    cert76_seen_46_6_3 cert76_layer_46_6_3_eq 24

theorem cert76_step_46_6 :
    closedCollarIndexStepBool word fiber76 46 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_46_6)
    (by decide) (by decide)
    (by simpa [cert76_move_46_6] using cert76_component_46_6_eq)
    (by decide) (by decide) (by decide)

def cert76_move_46_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_46_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_46_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_46_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_46_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.b LColor.p cert76_seen_46_30_0 = cert76_layer_46_30_0 := by
  decide

def cert76_seen_46_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_46_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_46_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.b LColor.p cert76_seen_46_30_1 = cert76_layer_46_30_1 := by
  decide

def cert76_seen_46_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_46_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_46_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.b LColor.p cert76_seen_46_30_2 = cert76_layer_46_30_2 := by
  decide

def cert76_seen_46_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_46_30_3 : List ChainEdge :=
  []

theorem cert76_layer_46_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 46 [])
      LColor.b LColor.p cert76_seen_46_30_3 = cert76_layer_46_30_3 := by
  decide

theorem cert76_component_46_30_eq :
    closedCollarComponent word (listGetD fiber76 46 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_46_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 46 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.b LColor.p 27 cert76_seen_46_30_0 = cert76_component_46_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.b LColor.p
    cert76_seen_46_30_0 cert76_layer_46_30_0 26 cert76_layer_46_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.b LColor.p 26 cert76_seen_46_30_1 = cert76_component_46_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.b LColor.p
    cert76_seen_46_30_1 cert76_layer_46_30_1 25 cert76_layer_46_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.b LColor.p 25 cert76_seen_46_30_2 = cert76_component_46_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 46 []) LColor.b LColor.p
    cert76_seen_46_30_2 cert76_layer_46_30_2 24 cert76_layer_46_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 46 [])
      LColor.b LColor.p 24 cert76_seen_46_30_3 = cert76_component_46_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 46 []) LColor.b LColor.p
    cert76_seen_46_30_3 cert76_layer_46_30_3_eq 24

theorem cert76_step_46_30 :
    closedCollarIndexStepBool word fiber76 46 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_46_30)
    (by decide) (by decide)
    (by simpa [cert76_move_46_30] using cert76_component_46_30_eq)
    (by decide) (by decide) (by decide)

def cert76_move_47_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert76_component_47_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_seen_47_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert76_layer_47_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert76_layer_47_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.r LColor.p cert76_seen_47_7_0 = cert76_layer_47_7_0 := by
  decide

def cert76_seen_47_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert76_layer_47_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert76_layer_47_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.r LColor.p cert76_seen_47_7_1 = cert76_layer_47_7_1 := by
  decide

def cert76_seen_47_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert76_layer_47_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert76_layer_47_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.r LColor.p cert76_seen_47_7_2 = cert76_layer_47_7_2 := by
  decide

def cert76_seen_47_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert76_layer_47_7_3 : List ChainEdge :=
  []

theorem cert76_layer_47_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.r LColor.p cert76_seen_47_7_3 = cert76_layer_47_7_3 := by
  decide

theorem cert76_component_47_7_eq :
    closedCollarComponent word (listGetD fiber76 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert76_component_47_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.r LColor.p 27 cert76_seen_47_7_0 = cert76_component_47_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.r LColor.p
    cert76_seen_47_7_0 cert76_layer_47_7_0 26 cert76_layer_47_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.r LColor.p 26 cert76_seen_47_7_1 = cert76_component_47_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.r LColor.p
    cert76_seen_47_7_1 cert76_layer_47_7_1 25 cert76_layer_47_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.r LColor.p 25 cert76_seen_47_7_2 = cert76_component_47_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.r LColor.p
    cert76_seen_47_7_2 cert76_layer_47_7_2 24 cert76_layer_47_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.r LColor.p 24 cert76_seen_47_7_3 = cert76_component_47_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 47 []) LColor.r LColor.p
    cert76_seen_47_7_3 cert76_layer_47_7_3_eq 24

theorem cert76_step_47_7 :
    closedCollarIndexStepBool word fiber76 47 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_47_7)
    (by decide) (by decide)
    (by simpa [cert76_move_47_7] using cert76_component_47_7_eq)
    (by decide) (by decide) (by decide)

def cert76_move_47_31 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert76_component_47_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_seen_47_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert76_layer_47_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert76_layer_47_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.b LColor.p cert76_seen_47_31_0 = cert76_layer_47_31_0 := by
  decide

def cert76_seen_47_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert76_layer_47_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert76_layer_47_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.b LColor.p cert76_seen_47_31_1 = cert76_layer_47_31_1 := by
  decide

def cert76_seen_47_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert76_layer_47_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert76_layer_47_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.b LColor.p cert76_seen_47_31_2 = cert76_layer_47_31_2 := by
  decide

def cert76_seen_47_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert76_layer_47_31_3 : List ChainEdge :=
  []

theorem cert76_layer_47_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber76 47 [])
      LColor.b LColor.p cert76_seen_47_31_3 = cert76_layer_47_31_3 := by
  decide

theorem cert76_component_47_31_eq :
    closedCollarComponent word (listGetD fiber76 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert76_component_47_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber76 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.b LColor.p 27 cert76_seen_47_31_0 = cert76_component_47_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.b LColor.p
    cert76_seen_47_31_0 cert76_layer_47_31_0 26 cert76_layer_47_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.b LColor.p 26 cert76_seen_47_31_1 = cert76_component_47_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.b LColor.p
    cert76_seen_47_31_1 cert76_layer_47_31_1 25 cert76_layer_47_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.b LColor.p 25 cert76_seen_47_31_2 = cert76_component_47_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber76 47 []) LColor.b LColor.p
    cert76_seen_47_31_2 cert76_layer_47_31_2 24 cert76_layer_47_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber76 47 [])
      LColor.b LColor.p 24 cert76_seen_47_31_3 = cert76_component_47_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber76 47 []) LColor.b LColor.p
    cert76_seen_47_31_3 cert76_layer_47_31_3_eq 24

theorem cert76_step_47_31 :
    closedCollarIndexStepBool word fiber76 47 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert76_move_47_31)
    (by decide) (by decide)
    (by simpa [cert76_move_47_31] using cert76_component_47_31_eq)
    (by decide) (by decide) (by decide)

theorem cert76_row_0 :
    closedCollarParentIndexValid word fiber76 cert76.parents 0 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length]

theorem cert76_row_1 :
    closedCollarParentIndexValid word fiber76 cert76.parents 1 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_1_0, cert76_step_0_1]

theorem cert76_row_2 :
    closedCollarParentIndexValid word fiber76 cert76.parents 2 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_2_0, cert76_step_0_2]

theorem cert76_row_3 :
    closedCollarParentIndexValid word fiber76 cert76.parents 3 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_3_1, cert76_step_1_3]

theorem cert76_row_4 :
    closedCollarParentIndexValid word fiber76 cert76.parents 4 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_4_2, cert76_step_2_4]

theorem cert76_row_5 :
    closedCollarParentIndexValid word fiber76 cert76.parents 5 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_5_7, cert76_step_7_5]

theorem cert76_row_6 :
    closedCollarParentIndexValid word fiber76 cert76.parents 6 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_6_1, cert76_step_1_6]

theorem cert76_row_7 :
    closedCollarParentIndexValid word fiber76 cert76.parents 7 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_7_0, cert76_step_0_7]

theorem cert76_row_8 :
    closedCollarParentIndexValid word fiber76 cert76.parents 8 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_8_0, cert76_step_0_8]

theorem cert76_row_9 :
    closedCollarParentIndexValid word fiber76 cert76.parents 9 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_9_1, cert76_step_1_9]

theorem cert76_row_10 :
    closedCollarParentIndexValid word fiber76 cert76.parents 10 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_10_2, cert76_step_2_10]

theorem cert76_row_11 :
    closedCollarParentIndexValid word fiber76 cert76.parents 11 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_11_3, cert76_step_3_11]

theorem cert76_row_12 :
    closedCollarParentIndexValid word fiber76 cert76.parents 12 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_12_4, cert76_step_4_12]

theorem cert76_row_13 :
    closedCollarParentIndexValid word fiber76 cert76.parents 13 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_13_5, cert76_step_5_13]

theorem cert76_row_14 :
    closedCollarParentIndexValid word fiber76 cert76.parents 14 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_14_6, cert76_step_6_14]

theorem cert76_row_15 :
    closedCollarParentIndexValid word fiber76 cert76.parents 15 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_15_7, cert76_step_7_15]

theorem cert76_row_16 :
    closedCollarParentIndexValid word fiber76 cert76.parents 16 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_16_0, cert76_step_0_16]

theorem cert76_row_17 :
    closedCollarParentIndexValid word fiber76 cert76.parents 17 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_17_1, cert76_step_1_17]

theorem cert76_row_18 :
    closedCollarParentIndexValid word fiber76 cert76.parents 18 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_18_2, cert76_step_2_18]

theorem cert76_row_19 :
    closedCollarParentIndexValid word fiber76 cert76.parents 19 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_19_3, cert76_step_3_19]

theorem cert76_row_20 :
    closedCollarParentIndexValid word fiber76 cert76.parents 20 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_20_8, cert76_step_8_20]

theorem cert76_row_21 :
    closedCollarParentIndexValid word fiber76 cert76.parents 21 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_21_9, cert76_step_9_21]

theorem cert76_row_22 :
    closedCollarParentIndexValid word fiber76 cert76.parents 22 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_22_10, cert76_step_10_22]

theorem cert76_row_23 :
    closedCollarParentIndexValid word fiber76 cert76.parents 23 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_23_11, cert76_step_11_23]

theorem cert76_row_24 :
    closedCollarParentIndexValid word fiber76 cert76.parents 24 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_24_18, cert76_step_18_24]

theorem cert76_row_25 :
    closedCollarParentIndexValid word fiber76 cert76.parents 25 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_25_27, cert76_step_27_25]

theorem cert76_row_26 :
    closedCollarParentIndexValid word fiber76 cert76.parents 26 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_26_17, cert76_step_17_26]

theorem cert76_row_27 :
    closedCollarParentIndexValid word fiber76 cert76.parents 27 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_27_16, cert76_step_16_27]

theorem cert76_row_28 :
    closedCollarParentIndexValid word fiber76 cert76.parents 28 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_28_44, cert76_step_44_28]

theorem cert76_row_29 :
    closedCollarParentIndexValid word fiber76 cert76.parents 29 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_29_45, cert76_step_45_29]

theorem cert76_row_30 :
    closedCollarParentIndexValid word fiber76 cert76.parents 30 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_30_46, cert76_step_46_30]

theorem cert76_row_31 :
    closedCollarParentIndexValid word fiber76 cert76.parents 31 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_31_47, cert76_step_47_31]

theorem cert76_row_32 :
    closedCollarParentIndexValid word fiber76 cert76.parents 32 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_32_8, cert76_step_8_32]

theorem cert76_row_33 :
    closedCollarParentIndexValid word fiber76 cert76.parents 33 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_33_9, cert76_step_9_33]

theorem cert76_row_34 :
    closedCollarParentIndexValid word fiber76 cert76.parents 34 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_34_10, cert76_step_10_34]

theorem cert76_row_35 :
    closedCollarParentIndexValid word fiber76 cert76.parents 35 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_35_11, cert76_step_11_35]

theorem cert76_row_36 :
    closedCollarParentIndexValid word fiber76 cert76.parents 36 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_36_12, cert76_step_12_36]

theorem cert76_row_37 :
    closedCollarParentIndexValid word fiber76 cert76.parents 37 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_37_13, cert76_step_13_37]

theorem cert76_row_38 :
    closedCollarParentIndexValid word fiber76 cert76.parents 38 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_38_14, cert76_step_14_38]

theorem cert76_row_39 :
    closedCollarParentIndexValid word fiber76 cert76.parents 39 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_39_15, cert76_step_15_39]

theorem cert76_row_40 :
    closedCollarParentIndexValid word fiber76 cert76.parents 40 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_40_0, cert76_step_0_40]

theorem cert76_row_41 :
    closedCollarParentIndexValid word fiber76 cert76.parents 41 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_41_1, cert76_step_1_41]

theorem cert76_row_42 :
    closedCollarParentIndexValid word fiber76 cert76.parents 42 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_42_2, cert76_step_2_42]

theorem cert76_row_43 :
    closedCollarParentIndexValid word fiber76 cert76.parents 43 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_43_3, cert76_step_3_43]

theorem cert76_row_44 :
    closedCollarParentIndexValid word fiber76 cert76.parents 44 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_44_4, cert76_step_4_44]

theorem cert76_row_45 :
    closedCollarParentIndexValid word fiber76 cert76.parents 45 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_45_5, cert76_step_5_45]

theorem cert76_row_46 :
    closedCollarParentIndexValid word fiber76 cert76.parents 46 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_46_6, cert76_step_6_46]

theorem cert76_row_47 :
    closedCollarParentIndexValid word fiber76 cert76.parents 47 = true := by
  have cert76_fiber_length : fiber76.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert76, listGetD, cert76_fiber_length, cert76_step_47_7, cert76_step_7_47]

theorem cert76_rows :
    closedCollarSpineRowsValid word fiber76 cert76.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert76_fiber_length : fiber76.length = 48 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert76_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert76_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert76_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert76_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert76_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert76_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert76_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert76_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert76_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert76_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert76_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert76_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert76_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert76_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert76_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert76_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert76_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert76_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert76_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert76_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert76_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert76_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert76_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert76_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert76_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert76_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert76_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert76_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert76_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert76_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert76_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert76_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert76_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert76_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert76_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert76_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert76_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert76_row_43
  by_cases h44 : idx = 44
  · subst idx
    exact cert76_row_44
  by_cases h45 : idx = 45
  · subst idx
    exact cert76_row_45
  by_cases h46 : idx = 46
  · subst idx
    exact cert76_row_46
  by_cases h47 : idx = 47
  · subst idx
    exact cert76_row_47
  · omega

theorem cert76_root :
    closedCollarSpineParentsReachRoot fiber76 cert76 = true := by
  decide

theorem cert76_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.b] := by
  change closedCollarFiberKempeConnected word cert76.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert76 fiber76_eq cert76_rows cert76_root


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
