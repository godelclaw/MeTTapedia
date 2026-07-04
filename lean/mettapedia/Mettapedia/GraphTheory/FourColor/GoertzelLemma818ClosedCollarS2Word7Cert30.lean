import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast30 : List TauState :=
  [stateAt 103, stateAt 111, stateAt 119, stateAt 127, stateAt 167, stateAt 175, stateAt 183, stateAt 191]

theorem keyedLast30_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.b, LColor.r]) =
      keyedLast30 := by
  decide

def fiber30OuterChunks : List (List (List TauState)) :=
[
  [
  [stateAt 0, stateAt 156, stateAt 167]
, [stateAt 0, stateAt 157, stateAt 175]
, [stateAt 0, stateAt 172, stateAt 183]
, [stateAt 0, stateAt 173, stateAt 191]
, [stateAt 0, stateAt 174, stateAt 119]
, [stateAt 0, stateAt 175, stateAt 127]
, [stateAt 1, stateAt 148, stateAt 167]
, [stateAt 1, stateAt 149, stateAt 175]
, [stateAt 1, stateAt 164, stateAt 183]
, [stateAt 1, stateAt 165, stateAt 191]
, [stateAt 1, stateAt 166, stateAt 119]
, [stateAt 1, stateAt 167, stateAt 127]
, [stateAt 2, stateAt 140, stateAt 167]
, [stateAt 2, stateAt 141, stateAt 175]
, [stateAt 2, stateAt 188, stateAt 183]
, [stateAt 2, stateAt 189, stateAt 191]
, [stateAt 2, stateAt 190, stateAt 119]
, [stateAt 2, stateAt 191, stateAt 127]
, [stateAt 3, stateAt 132, stateAt 167]
, [stateAt 3, stateAt 133, stateAt 175]
, [stateAt 3, stateAt 180, stateAt 183]
, [stateAt 3, stateAt 181, stateAt 191]
, [stateAt 3, stateAt 182, stateAt 119]
, [stateAt 3, stateAt 183, stateAt 127]
]
, []
, []
, [
  [stateAt 48, stateAt 88, stateAt 103]
, [stateAt 48, stateAt 89, stateAt 111]
, [stateAt 48, stateAt 108, stateAt 183]
, [stateAt 48, stateAt 109, stateAt 191]
, [stateAt 48, stateAt 110, stateAt 119]
, [stateAt 48, stateAt 111, stateAt 127]
, [stateAt 49, stateAt 80, stateAt 103]
, [stateAt 49, stateAt 81, stateAt 111]
, [stateAt 49, stateAt 100, stateAt 183]
, [stateAt 49, stateAt 101, stateAt 191]
, [stateAt 49, stateAt 102, stateAt 119]
, [stateAt 49, stateAt 103, stateAt 127]
, [stateAt 50, stateAt 72, stateAt 103]
, [stateAt 50, stateAt 73, stateAt 111]
, [stateAt 50, stateAt 124, stateAt 183]
, [stateAt 50, stateAt 125, stateAt 191]
, [stateAt 50, stateAt 126, stateAt 119]
, [stateAt 50, stateAt 127, stateAt 127]
, [stateAt 51, stateAt 64, stateAt 103]
, [stateAt 51, stateAt 65, stateAt 111]
, [stateAt 51, stateAt 116, stateAt 183]
, [stateAt 51, stateAt 117, stateAt 191]
, [stateAt 51, stateAt 118, stateAt 119]
, [stateAt 51, stateAt 119, stateAt 127]
]
, []
, []
, []
, []
, []
, []
, []
, []
]

def fiber30 : List (List TauState) :=
  fiber30OuterChunks.flatten

theorem fiber30_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 0 []) =
      listGetD fiber30OuterChunks 0 [] := by
  decide

theorem fiber30_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 1 []) =
      listGetD fiber30OuterChunks 1 [] := by
  decide

theorem fiber30_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 2 []) =
      listGetD fiber30OuterChunks 2 [] := by
  decide

theorem fiber30_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 3 []) =
      listGetD fiber30OuterChunks 3 [] := by
  decide

theorem fiber30_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 4 []) =
      listGetD fiber30OuterChunks 4 [] := by
  decide

theorem fiber30_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 5 []) =
      listGetD fiber30OuterChunks 5 [] := by
  decide

theorem fiber30_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 6 []) =
      listGetD fiber30OuterChunks 6 [] := by
  decide

theorem fiber30_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 7 []) =
      listGetD fiber30OuterChunks 7 [] := by
  decide

theorem fiber30_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 8 []) =
      listGetD fiber30OuterChunks 8 [] := by
  decide

theorem fiber30_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 9 []) =
      listGetD fiber30OuterChunks 9 [] := by
  decide

theorem fiber30_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 10 []) =
      listGetD fiber30OuterChunks 10 [] := by
  decide

theorem fiber30_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks 11 []) =
      listGetD fiber30OuterChunks 11 [] := by
  decide

theorem fiber30_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast30
        (listGetD tauStateChunks idx []) =
      listGetD fiber30OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber30_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber30_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber30_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber30_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber30_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber30_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber30_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber30_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber30_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber30_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber30_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber30_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber30_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast30 =
      fiber30 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast30 tauStateChunks fiber30OuterChunks
    tauStateChunks_eq (by rfl) fiber30_outer_get
  simpa [fiber30] using h

theorem fiber30_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.b, LColor.r] = fiber30 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.b, LColor.r] keyedLast30_eq
  exact hfrom.trans fiber30_keyedFrom_eq

theorem fiber30_eq :
    closedCollarFiber word [LColor.b, LColor.r, LColor.b, LColor.r] = fiber30 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.b, LColor.r, LColor.b, LColor.r]
  exact hfast.trans fiber30_keyed_eq

def cert30 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.r, LColor.b, LColor.r],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 47, 0, 1, 2, 3, 25, 24, 6, 7, 8, 9, 31, 30, 12, 13, 14, 15, 37, 36, 24, 25, 26, 27, 28, 29] }

def cert30_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert30_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert30_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_1_0 = cert30_layer_0_1_0 := by
  decide

def cert30_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_0_1_1 : List ChainEdge :=
  []

theorem cert30_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_1_1 = cert30_layer_0_1_1 := by
  decide

theorem cert30_component_0_1_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert30_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 27 cert30_seen_0_1_0 = cert30_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_1_0 cert30_layer_0_1_0 26 cert30_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 26 cert30_seen_0_1_1 = cert30_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_1_1 cert30_layer_0_1_1_eq 26

theorem cert30_step_0_1 :
    closedCollarIndexStepBool word fiber30 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_1)
    (by decide) (by decide)
    (by simpa [cert30_move_0_1] using cert30_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_2_0 = cert30_layer_0_2_0 := by
  decide

def cert30_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_2_1 = cert30_layer_0_2_1 := by
  decide

def cert30_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_2_2 = cert30_layer_0_2_2 := by
  decide

def cert30_seen_0_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_0_2_3 : List ChainEdge :=
  []

theorem cert30_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_2_3 = cert30_layer_0_2_3 := by
  decide

theorem cert30_component_0_2_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert30_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 27 cert30_seen_0_2_0 = cert30_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_2_0 cert30_layer_0_2_0 26 cert30_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 26 cert30_seen_0_2_1 = cert30_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_2_1 cert30_layer_0_2_1 25 cert30_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 25 cert30_seen_0_2_2 = cert30_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_2_2 cert30_layer_0_2_2 24 cert30_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 24 cert30_seen_0_2_3 = cert30_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_2_3 cert30_layer_0_2_3_eq 24

theorem cert30_step_0_2 :
    closedCollarIndexStepBool word fiber30 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_2)
    (by decide) (by decide)
    (by simpa [cert30_move_0_2] using cert30_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_0_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_6_0 = cert30_layer_0_6_0 := by
  decide

def cert30_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_0_6_1 : List ChainEdge :=
  []

theorem cert30_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_6_1 = cert30_layer_0_6_1 := by
  decide

theorem cert30_component_0_6_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 27 cert30_seen_0_6_0 = cert30_component_0_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_6_0 cert30_layer_0_6_0 26 cert30_layer_0_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 26 cert30_seen_0_6_1 = cert30_component_0_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_6_1 cert30_layer_0_6_1_eq 26

theorem cert30_step_0_6 :
    closedCollarIndexStepBool word fiber30 0 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_6)
    (by decide) (by decide)
    (by simpa [cert30_move_0_6] using cert30_component_0_6_eq)
    (by decide) (by decide) (by decide)

def cert30_move_0_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_0_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_0_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_12_0 = cert30_layer_0_12_0 := by
  decide

def cert30_seen_0_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_0_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_0_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_12_1 = cert30_layer_0_12_1 := by
  decide

def cert30_seen_0_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_0_12_2 : List ChainEdge :=
  []

theorem cert30_layer_0_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.r LColor.b cert30_seen_0_12_2 = cert30_layer_0_12_2 := by
  decide

theorem cert30_component_0_12_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_0_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 27 cert30_seen_0_12_0 = cert30_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_12_0 cert30_layer_0_12_0 26 cert30_layer_0_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 26 cert30_seen_0_12_1 = cert30_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_12_1 cert30_layer_0_12_1 25 cert30_layer_0_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.r LColor.b 25 cert30_seen_0_12_2 = cert30_component_0_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.r LColor.b
    cert30_seen_0_12_2 cert30_layer_0_12_2_eq 25

theorem cert30_step_0_12 :
    closedCollarIndexStepBool word fiber30 0 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_12)
    (by decide) (by decide)
    (by simpa [cert30_move_0_12] using cert30_component_0_12_eq)
    (by decide) (by decide) (by decide)

def cert30_move_0_24 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_0_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_0_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_0 = cert30_layer_0_24_0 := by
  decide

def cert30_seen_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_0_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_1 = cert30_layer_0_24_1 := by
  decide

def cert30_seen_0_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_0_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_0_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_2 = cert30_layer_0_24_2 := by
  decide

def cert30_seen_0_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_0_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_0_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_3 = cert30_layer_0_24_3 := by
  decide

def cert30_seen_0_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_0_24_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_0_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_4 = cert30_layer_0_24_4 := by
  decide

def cert30_seen_0_24_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_0_24_5 : List ChainEdge :=
  []

theorem cert30_layer_0_24_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 0 [])
      LColor.b LColor.p cert30_seen_0_24_5 = cert30_layer_0_24_5 := by
  decide

theorem cert30_component_0_24_eq :
    closedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_0_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 27 cert30_seen_0_24_0 = cert30_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_0 cert30_layer_0_24_0 26 cert30_layer_0_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 26 cert30_seen_0_24_1 = cert30_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_1 cert30_layer_0_24_1 25 cert30_layer_0_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 25 cert30_seen_0_24_2 = cert30_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_2 cert30_layer_0_24_2 24 cert30_layer_0_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 24 cert30_seen_0_24_3 = cert30_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_3 cert30_layer_0_24_3 23 cert30_layer_0_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 23 cert30_seen_0_24_4 = cert30_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_4 cert30_layer_0_24_4 22 cert30_layer_0_24_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 0 [])
      LColor.b LColor.p 22 cert30_seen_0_24_5 = cert30_component_0_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 0 []) LColor.b LColor.p
    cert30_seen_0_24_5 cert30_layer_0_24_5_eq 22

theorem cert30_step_0_24 :
    closedCollarIndexStepBool word fiber30 0 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_0_24)
    (by decide) (by decide)
    (by simpa [cert30_move_0_24] using cert30_component_0_24_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert30_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert30_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_0_0 = cert30_layer_1_0_0 := by
  decide

def cert30_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_1_0_1 : List ChainEdge :=
  []

theorem cert30_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_0_1 = cert30_layer_1_0_1 := by
  decide

theorem cert30_component_1_0_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert30_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 27 cert30_seen_1_0_0 = cert30_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_0_0 cert30_layer_1_0_0 26 cert30_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 26 cert30_seen_1_0_1 = cert30_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_0_1 cert30_layer_1_0_1_eq 26

theorem cert30_step_1_0 :
    closedCollarIndexStepBool word fiber30 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_0)
    (by decide) (by decide)
    (by simpa [cert30_move_1_0] using cert30_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_3_0 = cert30_layer_1_3_0 := by
  decide

def cert30_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_3_1 = cert30_layer_1_3_1 := by
  decide

def cert30_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_3_2 = cert30_layer_1_3_2 := by
  decide

def cert30_seen_1_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_1_3_3 : List ChainEdge :=
  []

theorem cert30_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_3_3 = cert30_layer_1_3_3 := by
  decide

theorem cert30_component_1_3_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert30_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 27 cert30_seen_1_3_0 = cert30_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_3_0 cert30_layer_1_3_0 26 cert30_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 26 cert30_seen_1_3_1 = cert30_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_3_1 cert30_layer_1_3_1 25 cert30_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 25 cert30_seen_1_3_2 = cert30_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_3_2 cert30_layer_1_3_2 24 cert30_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 24 cert30_seen_1_3_3 = cert30_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_3_3 cert30_layer_1_3_3_eq 24

theorem cert30_step_1_3 :
    closedCollarIndexStepBool word fiber30 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_3)
    (by decide) (by decide)
    (by simpa [cert30_move_1_3] using cert30_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_7_0 = cert30_layer_1_7_0 := by
  decide

def cert30_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_1_7_1 : List ChainEdge :=
  []

theorem cert30_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_7_1 = cert30_layer_1_7_1 := by
  decide

theorem cert30_component_1_7_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 27 cert30_seen_1_7_0 = cert30_component_1_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_7_0 cert30_layer_1_7_0 26 cert30_layer_1_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 26 cert30_seen_1_7_1 = cert30_component_1_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_7_1 cert30_layer_1_7_1_eq 26

theorem cert30_step_1_7 :
    closedCollarIndexStepBool word fiber30 1 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_7)
    (by decide) (by decide)
    (by simpa [cert30_move_1_7] using cert30_component_1_7_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_1_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_1_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_13_0 = cert30_layer_1_13_0 := by
  decide

def cert30_seen_1_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_1_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_1_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_13_1 = cert30_layer_1_13_1 := by
  decide

def cert30_seen_1_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_1_13_2 : List ChainEdge :=
  []

theorem cert30_layer_1_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.r LColor.b cert30_seen_1_13_2 = cert30_layer_1_13_2 := by
  decide

theorem cert30_component_1_13_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_1_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 27 cert30_seen_1_13_0 = cert30_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_13_0 cert30_layer_1_13_0 26 cert30_layer_1_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 26 cert30_seen_1_13_1 = cert30_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_13_1 cert30_layer_1_13_1 25 cert30_layer_1_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.r LColor.b 25 cert30_seen_1_13_2 = cert30_component_1_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.r LColor.b
    cert30_seen_1_13_2 cert30_layer_1_13_2_eq 25

theorem cert30_step_1_13 :
    closedCollarIndexStepBool word fiber30 1 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_13)
    (by decide) (by decide)
    (by simpa [cert30_move_1_13] using cert30_component_1_13_eq)
    (by decide) (by decide) (by decide)

def cert30_move_1_25 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_1_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_1_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_0 = cert30_layer_1_25_0 := by
  decide

def cert30_seen_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_1_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_1 = cert30_layer_1_25_1 := by
  decide

def cert30_seen_1_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_1_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_1_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_2 = cert30_layer_1_25_2 := by
  decide

def cert30_seen_1_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_1_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_1_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_3 = cert30_layer_1_25_3 := by
  decide

def cert30_seen_1_25_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_1_25_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_1_25_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_4 = cert30_layer_1_25_4 := by
  decide

def cert30_seen_1_25_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_1_25_5 : List ChainEdge :=
  []

theorem cert30_layer_1_25_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 1 [])
      LColor.b LColor.p cert30_seen_1_25_5 = cert30_layer_1_25_5 := by
  decide

theorem cert30_component_1_25_eq :
    closedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_1_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 27 cert30_seen_1_25_0 = cert30_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_0 cert30_layer_1_25_0 26 cert30_layer_1_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 26 cert30_seen_1_25_1 = cert30_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_1 cert30_layer_1_25_1 25 cert30_layer_1_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 25 cert30_seen_1_25_2 = cert30_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_2 cert30_layer_1_25_2 24 cert30_layer_1_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 24 cert30_seen_1_25_3 = cert30_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_3 cert30_layer_1_25_3 23 cert30_layer_1_25_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 23 cert30_seen_1_25_4 = cert30_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_4 cert30_layer_1_25_4 22 cert30_layer_1_25_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 1 [])
      LColor.b LColor.p 22 cert30_seen_1_25_5 = cert30_component_1_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 1 []) LColor.b LColor.p
    cert30_seen_1_25_5 cert30_layer_1_25_5_eq 22

theorem cert30_step_1_25 :
    closedCollarIndexStepBool word fiber30 1 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_1_25)
    (by decide) (by decide)
    (by simpa [cert30_move_1_25] using cert30_component_1_25_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_0_0 = cert30_layer_2_0_0 := by
  decide

def cert30_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_0_1 = cert30_layer_2_0_1 := by
  decide

def cert30_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_0_2 = cert30_layer_2_0_2 := by
  decide

def cert30_seen_2_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_2_0_3 : List ChainEdge :=
  []

theorem cert30_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_0_3 = cert30_layer_2_0_3 := by
  decide

theorem cert30_component_2_0_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert30_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 27 cert30_seen_2_0_0 = cert30_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_0_0 cert30_layer_2_0_0 26 cert30_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 26 cert30_seen_2_0_1 = cert30_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_0_1 cert30_layer_2_0_1 25 cert30_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 25 cert30_seen_2_0_2 = cert30_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_0_2 cert30_layer_2_0_2 24 cert30_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 24 cert30_seen_2_0_3 = cert30_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_0_3 cert30_layer_2_0_3_eq 24

theorem cert30_step_2_0 :
    closedCollarIndexStepBool word fiber30 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_0)
    (by decide) (by decide)
    (by simpa [cert30_move_2_0] using cert30_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert30_component_2_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_seen_2_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert30_layer_2_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_2_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_0 = cert30_layer_2_4_0 := by
  decide

def cert30_seen_2_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_2_4_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_2_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_1 = cert30_layer_2_4_1 := by
  decide

def cert30_seen_2_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_2_4_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_2_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_2 = cert30_layer_2_4_2 := by
  decide

def cert30_seen_2_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_2_4_3 : List ChainEdge :=
  []

theorem cert30_layer_2_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_4_3 = cert30_layer_2_4_3 := by
  decide

theorem cert30_component_2_4_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert30_component_2_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 27 cert30_seen_2_4_0 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_0 cert30_layer_2_4_0 26 cert30_layer_2_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 26 cert30_seen_2_4_1 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_1 cert30_layer_2_4_1 25 cert30_layer_2_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 25 cert30_seen_2_4_2 = cert30_component_2_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_2 cert30_layer_2_4_2 24 cert30_layer_2_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 24 cert30_seen_2_4_3 = cert30_component_2_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_4_3 cert30_layer_2_4_3_eq 24

theorem cert30_step_2_4 :
    closedCollarIndexStepBool word fiber30 2 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_4)
    (by decide) (by decide)
    (by simpa [cert30_move_2_4] using cert30_component_2_4_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_8_0 = cert30_layer_2_8_0 := by
  decide

def cert30_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_2_8_1 : List ChainEdge :=
  []

theorem cert30_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_8_1 = cert30_layer_2_8_1 := by
  decide

theorem cert30_component_2_8_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 27 cert30_seen_2_8_0 = cert30_component_2_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_8_0 cert30_layer_2_8_0 26 cert30_layer_2_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 26 cert30_seen_2_8_1 = cert30_component_2_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_8_1 cert30_layer_2_8_1_eq 26

theorem cert30_step_2_8 :
    closedCollarIndexStepBool word fiber30 2 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_8)
    (by decide) (by decide)
    (by simpa [cert30_move_2_8] using cert30_component_2_8_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_2_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_2_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_14_0 = cert30_layer_2_14_0 := by
  decide

def cert30_seen_2_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_2_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_2_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_14_1 = cert30_layer_2_14_1 := by
  decide

def cert30_seen_2_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_2_14_2 : List ChainEdge :=
  []

theorem cert30_layer_2_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.r LColor.b cert30_seen_2_14_2 = cert30_layer_2_14_2 := by
  decide

theorem cert30_component_2_14_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_2_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 27 cert30_seen_2_14_0 = cert30_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_14_0 cert30_layer_2_14_0 26 cert30_layer_2_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 26 cert30_seen_2_14_1 = cert30_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_14_1 cert30_layer_2_14_1 25 cert30_layer_2_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.r LColor.b 25 cert30_seen_2_14_2 = cert30_component_2_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.r LColor.b
    cert30_seen_2_14_2 cert30_layer_2_14_2_eq 25

theorem cert30_step_2_14 :
    closedCollarIndexStepBool word fiber30 2 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_14)
    (by decide) (by decide)
    (by simpa [cert30_move_2_14] using cert30_component_2_14_eq)
    (by decide) (by decide) (by decide)

def cert30_move_2_26 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_2_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_2_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_26_0 = cert30_layer_2_26_0 := by
  decide

def cert30_seen_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_2_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_26_1 = cert30_layer_2_26_1 := by
  decide

def cert30_seen_2_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_2_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_2_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_26_2 = cert30_layer_2_26_2 := by
  decide

def cert30_seen_2_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_2_26_3 : List ChainEdge :=
  []

theorem cert30_layer_2_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 2 [])
      LColor.b LColor.p cert30_seen_2_26_3 = cert30_layer_2_26_3 := by
  decide

theorem cert30_component_2_26_eq :
    closedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_2_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 27 cert30_seen_2_26_0 = cert30_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_26_0 cert30_layer_2_26_0 26 cert30_layer_2_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 26 cert30_seen_2_26_1 = cert30_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_26_1 cert30_layer_2_26_1 25 cert30_layer_2_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 25 cert30_seen_2_26_2 = cert30_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_26_2 cert30_layer_2_26_2 24 cert30_layer_2_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 2 [])
      LColor.b LColor.p 24 cert30_seen_2_26_3 = cert30_component_2_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 2 []) LColor.b LColor.p
    cert30_seen_2_26_3 cert30_layer_2_26_3_eq 24

theorem cert30_step_2_26 :
    closedCollarIndexStepBool word fiber30 2 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_2_26)
    (by decide) (by decide)
    (by simpa [cert30_move_2_26] using cert30_component_2_26_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_1_0 = cert30_layer_3_1_0 := by
  decide

def cert30_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_1_1 = cert30_layer_3_1_1 := by
  decide

def cert30_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_1_2 = cert30_layer_3_1_2 := by
  decide

def cert30_seen_3_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_3_1_3 : List ChainEdge :=
  []

theorem cert30_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_1_3 = cert30_layer_3_1_3 := by
  decide

theorem cert30_component_3_1_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert30_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 27 cert30_seen_3_1_0 = cert30_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_1_0 cert30_layer_3_1_0 26 cert30_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 26 cert30_seen_3_1_1 = cert30_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_1_1 cert30_layer_3_1_1 25 cert30_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 25 cert30_seen_3_1_2 = cert30_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_1_2 cert30_layer_3_1_2 24 cert30_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 24 cert30_seen_3_1_3 = cert30_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_1_3 cert30_layer_3_1_3_eq 24

theorem cert30_step_3_1 :
    closedCollarIndexStepBool word fiber30 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_1)
    (by decide) (by decide)
    (by simpa [cert30_move_3_1] using cert30_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert30_component_3_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_seen_3_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert30_layer_3_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_3_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_0 = cert30_layer_3_5_0 := by
  decide

def cert30_seen_3_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_3_5_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_3_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_1 = cert30_layer_3_5_1 := by
  decide

def cert30_seen_3_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_3_5_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_3_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_2 = cert30_layer_3_5_2 := by
  decide

def cert30_seen_3_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_3_5_3 : List ChainEdge :=
  []

theorem cert30_layer_3_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_5_3 = cert30_layer_3_5_3 := by
  decide

theorem cert30_component_3_5_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert30_component_3_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 27 cert30_seen_3_5_0 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_0 cert30_layer_3_5_0 26 cert30_layer_3_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 26 cert30_seen_3_5_1 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_1 cert30_layer_3_5_1 25 cert30_layer_3_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 25 cert30_seen_3_5_2 = cert30_component_3_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_2 cert30_layer_3_5_2 24 cert30_layer_3_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 24 cert30_seen_3_5_3 = cert30_component_3_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_5_3 cert30_layer_3_5_3_eq 24

theorem cert30_step_3_5 :
    closedCollarIndexStepBool word fiber30 3 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_5)
    (by decide) (by decide)
    (by simpa [cert30_move_3_5] using cert30_component_3_5_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_9_0 = cert30_layer_3_9_0 := by
  decide

def cert30_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_3_9_1 : List ChainEdge :=
  []

theorem cert30_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_9_1 = cert30_layer_3_9_1 := by
  decide

theorem cert30_component_3_9_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 27 cert30_seen_3_9_0 = cert30_component_3_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_9_0 cert30_layer_3_9_0 26 cert30_layer_3_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 26 cert30_seen_3_9_1 = cert30_component_3_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_9_1 cert30_layer_3_9_1_eq 26

theorem cert30_step_3_9 :
    closedCollarIndexStepBool word fiber30 3 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_9)
    (by decide) (by decide)
    (by simpa [cert30_move_3_9] using cert30_component_3_9_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_3_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_3_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_15_0 = cert30_layer_3_15_0 := by
  decide

def cert30_seen_3_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_3_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_3_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_15_1 = cert30_layer_3_15_1 := by
  decide

def cert30_seen_3_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_3_15_2 : List ChainEdge :=
  []

theorem cert30_layer_3_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.r LColor.b cert30_seen_3_15_2 = cert30_layer_3_15_2 := by
  decide

theorem cert30_component_3_15_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_3_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 27 cert30_seen_3_15_0 = cert30_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_15_0 cert30_layer_3_15_0 26 cert30_layer_3_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 26 cert30_seen_3_15_1 = cert30_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_15_1 cert30_layer_3_15_1 25 cert30_layer_3_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.r LColor.b 25 cert30_seen_3_15_2 = cert30_component_3_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.r LColor.b
    cert30_seen_3_15_2 cert30_layer_3_15_2_eq 25

theorem cert30_step_3_15 :
    closedCollarIndexStepBool word fiber30 3 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_15)
    (by decide) (by decide)
    (by simpa [cert30_move_3_15] using cert30_component_3_15_eq)
    (by decide) (by decide) (by decide)

def cert30_move_3_27 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_3_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_3_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_27_0 = cert30_layer_3_27_0 := by
  decide

def cert30_seen_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_3_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_27_1 = cert30_layer_3_27_1 := by
  decide

def cert30_seen_3_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_3_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_3_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_27_2 = cert30_layer_3_27_2 := by
  decide

def cert30_seen_3_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_3_27_3 : List ChainEdge :=
  []

theorem cert30_layer_3_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 3 [])
      LColor.b LColor.p cert30_seen_3_27_3 = cert30_layer_3_27_3 := by
  decide

theorem cert30_component_3_27_eq :
    closedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_3_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 27 cert30_seen_3_27_0 = cert30_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_27_0 cert30_layer_3_27_0 26 cert30_layer_3_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 26 cert30_seen_3_27_1 = cert30_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_27_1 cert30_layer_3_27_1 25 cert30_layer_3_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 25 cert30_seen_3_27_2 = cert30_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_27_2 cert30_layer_3_27_2 24 cert30_layer_3_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 3 [])
      LColor.b LColor.p 24 cert30_seen_3_27_3 = cert30_component_3_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 3 []) LColor.b LColor.p
    cert30_seen_3_27_3 cert30_layer_3_27_3_eq 24

theorem cert30_step_3_27 :
    closedCollarIndexStepBool word fiber30 3 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_3_27)
    (by decide) (by decide)
    (by simpa [cert30_move_3_27] using cert30_component_3_27_eq)
    (by decide) (by decide) (by decide)

def cert30_move_4_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert30_component_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_seen_4_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert30_layer_4_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_4_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_0 = cert30_layer_4_2_0 := by
  decide

def cert30_seen_4_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_4_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_4_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_1 = cert30_layer_4_2_1 := by
  decide

def cert30_seen_4_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_4_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_4_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_2 = cert30_layer_4_2_2 := by
  decide

def cert30_seen_4_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_4_2_3 : List ChainEdge :=
  []

theorem cert30_layer_4_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_2_3 = cert30_layer_4_2_3 := by
  decide

theorem cert30_component_4_2_eq :
    closedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert30_component_4_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 27 cert30_seen_4_2_0 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_0 cert30_layer_4_2_0 26 cert30_layer_4_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 26 cert30_seen_4_2_1 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_1 cert30_layer_4_2_1 25 cert30_layer_4_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 25 cert30_seen_4_2_2 = cert30_component_4_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_2 cert30_layer_4_2_2 24 cert30_layer_4_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 24 cert30_seen_4_2_3 = cert30_component_4_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_2_3 cert30_layer_4_2_3_eq 24

theorem cert30_step_4_2 :
    closedCollarIndexStepBool word fiber30 4 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_4_2)
    (by decide) (by decide)
    (by simpa [cert30_move_4_2] using cert30_component_4_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_4_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_10_0 = cert30_layer_4_10_0 := by
  decide

def cert30_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_4_10_1 : List ChainEdge :=
  []

theorem cert30_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.b LColor.p cert30_seen_4_10_1 = cert30_layer_4_10_1 := by
  decide

theorem cert30_component_4_10_eq :
    closedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 27 cert30_seen_4_10_0 = cert30_component_4_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_10_0 cert30_layer_4_10_0 26 cert30_layer_4_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.b LColor.p 26 cert30_seen_4_10_1 = cert30_component_4_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 4 []) LColor.b LColor.p
    cert30_seen_4_10_1 cert30_layer_4_10_1_eq 26

theorem cert30_step_4_10 :
    closedCollarIndexStepBool word fiber30 4 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_4_10)
    (by decide) (by decide)
    (by simpa [cert30_move_4_10] using cert30_component_4_10_eq)
    (by decide) (by decide) (by decide)

def cert30_move_4_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_4_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_4_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.b cert30_seen_4_16_0 = cert30_layer_4_16_0 := by
  decide

def cert30_seen_4_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_4_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_4_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.b cert30_seen_4_16_1 = cert30_layer_4_16_1 := by
  decide

def cert30_seen_4_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_4_16_2 : List ChainEdge :=
  []

theorem cert30_layer_4_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 4 [])
      LColor.r LColor.b cert30_seen_4_16_2 = cert30_layer_4_16_2 := by
  decide

theorem cert30_component_4_16_eq :
    closedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_4_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.b 27 cert30_seen_4_16_0 = cert30_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.r LColor.b
    cert30_seen_4_16_0 cert30_layer_4_16_0 26 cert30_layer_4_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.b 26 cert30_seen_4_16_1 = cert30_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 4 []) LColor.r LColor.b
    cert30_seen_4_16_1 cert30_layer_4_16_1 25 cert30_layer_4_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 4 [])
      LColor.r LColor.b 25 cert30_seen_4_16_2 = cert30_component_4_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 4 []) LColor.r LColor.b
    cert30_seen_4_16_2 cert30_layer_4_16_2_eq 25

theorem cert30_step_4_16 :
    closedCollarIndexStepBool word fiber30 4 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_4_16)
    (by decide) (by decide)
    (by simpa [cert30_move_4_16] using cert30_component_4_16_eq)
    (by decide) (by decide) (by decide)

def cert30_move_5_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert30_component_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_seen_5_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert30_layer_5_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_5_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_0 = cert30_layer_5_3_0 := by
  decide

def cert30_seen_5_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_5_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_5_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_1 = cert30_layer_5_3_1 := by
  decide

def cert30_seen_5_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_5_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_5_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_2 = cert30_layer_5_3_2 := by
  decide

def cert30_seen_5_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_5_3_3 : List ChainEdge :=
  []

theorem cert30_layer_5_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_3_3 = cert30_layer_5_3_3 := by
  decide

theorem cert30_component_5_3_eq :
    closedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert30_component_5_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 27 cert30_seen_5_3_0 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_0 cert30_layer_5_3_0 26 cert30_layer_5_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 26 cert30_seen_5_3_1 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_1 cert30_layer_5_3_1 25 cert30_layer_5_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 25 cert30_seen_5_3_2 = cert30_component_5_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_2 cert30_layer_5_3_2 24 cert30_layer_5_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 24 cert30_seen_5_3_3 = cert30_component_5_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_3_3 cert30_layer_5_3_3_eq 24

theorem cert30_step_5_3 :
    closedCollarIndexStepBool word fiber30 5 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_5_3)
    (by decide) (by decide)
    (by simpa [cert30_move_5_3] using cert30_component_5_3_eq)
    (by decide) (by decide) (by decide)

def cert30_move_5_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_11_0 = cert30_layer_5_11_0 := by
  decide

def cert30_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_5_11_1 : List ChainEdge :=
  []

theorem cert30_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.b LColor.p cert30_seen_5_11_1 = cert30_layer_5_11_1 := by
  decide

theorem cert30_component_5_11_eq :
    closedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 27 cert30_seen_5_11_0 = cert30_component_5_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_11_0 cert30_layer_5_11_0 26 cert30_layer_5_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.b LColor.p 26 cert30_seen_5_11_1 = cert30_component_5_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 5 []) LColor.b LColor.p
    cert30_seen_5_11_1 cert30_layer_5_11_1_eq 26

theorem cert30_step_5_11 :
    closedCollarIndexStepBool word fiber30 5 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_5_11)
    (by decide) (by decide)
    (by simpa [cert30_move_5_11] using cert30_component_5_11_eq)
    (by decide) (by decide) (by decide)

def cert30_move_5_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_5_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_5_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.b cert30_seen_5_17_0 = cert30_layer_5_17_0 := by
  decide

def cert30_seen_5_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_5_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_5_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.b cert30_seen_5_17_1 = cert30_layer_5_17_1 := by
  decide

def cert30_seen_5_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_5_17_2 : List ChainEdge :=
  []

theorem cert30_layer_5_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 5 [])
      LColor.r LColor.b cert30_seen_5_17_2 = cert30_layer_5_17_2 := by
  decide

theorem cert30_component_5_17_eq :
    closedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_5_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.b 27 cert30_seen_5_17_0 = cert30_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.r LColor.b
    cert30_seen_5_17_0 cert30_layer_5_17_0 26 cert30_layer_5_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.b 26 cert30_seen_5_17_1 = cert30_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 5 []) LColor.r LColor.b
    cert30_seen_5_17_1 cert30_layer_5_17_1 25 cert30_layer_5_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 5 [])
      LColor.r LColor.b 25 cert30_seen_5_17_2 = cert30_component_5_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 5 []) LColor.r LColor.b
    cert30_seen_5_17_2 cert30_layer_5_17_2_eq 25

theorem cert30_step_5_17 :
    closedCollarIndexStepBool word fiber30 5 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_5_17)
    (by decide) (by decide)
    (by simpa [cert30_move_5_17] using cert30_component_5_17_eq)
    (by decide) (by decide) (by decide)

def cert30_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_0_0 = cert30_layer_6_0_0 := by
  decide

def cert30_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_6_0_1 : List ChainEdge :=
  []

theorem cert30_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_0_1 = cert30_layer_6_0_1 := by
  decide

theorem cert30_component_6_0_eq :
    closedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 27 cert30_seen_6_0_0 = cert30_component_6_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_0_0 cert30_layer_6_0_0 26 cert30_layer_6_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 26 cert30_seen_6_0_1 = cert30_component_6_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_0_1 cert30_layer_6_0_1_eq 26

theorem cert30_step_6_0 :
    closedCollarIndexStepBool word fiber30 6 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_6_0)
    (by decide) (by decide)
    (by simpa [cert30_move_6_0] using cert30_component_6_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_6_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_6_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_6_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.r LColor.b cert30_seen_6_18_0 = cert30_layer_6_18_0 := by
  decide

def cert30_seen_6_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_6_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_6_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.r LColor.b cert30_seen_6_18_1 = cert30_layer_6_18_1 := by
  decide

def cert30_seen_6_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_6_18_2 : List ChainEdge :=
  []

theorem cert30_layer_6_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.r LColor.b cert30_seen_6_18_2 = cert30_layer_6_18_2 := by
  decide

theorem cert30_component_6_18_eq :
    closedCollarComponent word (listGetD fiber30 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_6_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.r LColor.b 27 cert30_seen_6_18_0 = cert30_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.r LColor.b
    cert30_seen_6_18_0 cert30_layer_6_18_0 26 cert30_layer_6_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.r LColor.b 26 cert30_seen_6_18_1 = cert30_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.r LColor.b
    cert30_seen_6_18_1 cert30_layer_6_18_1 25 cert30_layer_6_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.r LColor.b 25 cert30_seen_6_18_2 = cert30_component_6_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 6 []) LColor.r LColor.b
    cert30_seen_6_18_2 cert30_layer_6_18_2_eq 25

theorem cert30_step_6_18 :
    closedCollarIndexStepBool word fiber30 6 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_6_18)
    (by decide) (by decide)
    (by simpa [cert30_move_6_18] using cert30_component_6_18_eq)
    (by decide) (by decide) (by decide)

def cert30_move_6_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_6_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_6_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_0 = cert30_layer_6_30_0 := by
  decide

def cert30_seen_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_6_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_1 = cert30_layer_6_30_1 := by
  decide

def cert30_seen_6_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_6_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_6_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_2 = cert30_layer_6_30_2 := by
  decide

def cert30_seen_6_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_6_30_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_6_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_3 = cert30_layer_6_30_3 := by
  decide

def cert30_seen_6_30_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_6_30_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_6_30_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_4 = cert30_layer_6_30_4 := by
  decide

def cert30_seen_6_30_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_6_30_5 : List ChainEdge :=
  []

theorem cert30_layer_6_30_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 6 [])
      LColor.b LColor.p cert30_seen_6_30_5 = cert30_layer_6_30_5 := by
  decide

theorem cert30_component_6_30_eq :
    closedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_6_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 27 cert30_seen_6_30_0 = cert30_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_0 cert30_layer_6_30_0 26 cert30_layer_6_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 26 cert30_seen_6_30_1 = cert30_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_1 cert30_layer_6_30_1 25 cert30_layer_6_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 25 cert30_seen_6_30_2 = cert30_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_2 cert30_layer_6_30_2 24 cert30_layer_6_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 24 cert30_seen_6_30_3 = cert30_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_3 cert30_layer_6_30_3 23 cert30_layer_6_30_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 23 cert30_seen_6_30_4 = cert30_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_4 cert30_layer_6_30_4 22 cert30_layer_6_30_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 6 [])
      LColor.b LColor.p 22 cert30_seen_6_30_5 = cert30_component_6_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 6 []) LColor.b LColor.p
    cert30_seen_6_30_5 cert30_layer_6_30_5_eq 22

theorem cert30_step_6_30 :
    closedCollarIndexStepBool word fiber30 6 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_6_30)
    (by decide) (by decide)
    (by simpa [cert30_move_6_30] using cert30_component_6_30_eq)
    (by decide) (by decide) (by decide)

def cert30_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_1_0 = cert30_layer_7_1_0 := by
  decide

def cert30_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_7_1_1 : List ChainEdge :=
  []

theorem cert30_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_1_1 = cert30_layer_7_1_1 := by
  decide

theorem cert30_component_7_1_eq :
    closedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 27 cert30_seen_7_1_0 = cert30_component_7_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_1_0 cert30_layer_7_1_0 26 cert30_layer_7_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 26 cert30_seen_7_1_1 = cert30_component_7_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_1_1 cert30_layer_7_1_1_eq 26

theorem cert30_step_7_1 :
    closedCollarIndexStepBool word fiber30 7 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_7_1)
    (by decide) (by decide)
    (by simpa [cert30_move_7_1] using cert30_component_7_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_7_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_7_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_7_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.r LColor.b cert30_seen_7_19_0 = cert30_layer_7_19_0 := by
  decide

def cert30_seen_7_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_7_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_7_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.r LColor.b cert30_seen_7_19_1 = cert30_layer_7_19_1 := by
  decide

def cert30_seen_7_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_7_19_2 : List ChainEdge :=
  []

theorem cert30_layer_7_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.r LColor.b cert30_seen_7_19_2 = cert30_layer_7_19_2 := by
  decide

theorem cert30_component_7_19_eq :
    closedCollarComponent word (listGetD fiber30 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_7_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.r LColor.b 27 cert30_seen_7_19_0 = cert30_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.r LColor.b
    cert30_seen_7_19_0 cert30_layer_7_19_0 26 cert30_layer_7_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.r LColor.b 26 cert30_seen_7_19_1 = cert30_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.r LColor.b
    cert30_seen_7_19_1 cert30_layer_7_19_1 25 cert30_layer_7_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.r LColor.b 25 cert30_seen_7_19_2 = cert30_component_7_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 7 []) LColor.r LColor.b
    cert30_seen_7_19_2 cert30_layer_7_19_2_eq 25

theorem cert30_step_7_19 :
    closedCollarIndexStepBool word fiber30 7 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_7_19)
    (by decide) (by decide)
    (by simpa [cert30_move_7_19] using cert30_component_7_19_eq)
    (by decide) (by decide) (by decide)

def cert30_move_7_31 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_7_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_7_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_0 = cert30_layer_7_31_0 := by
  decide

def cert30_seen_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_7_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_1 = cert30_layer_7_31_1 := by
  decide

def cert30_seen_7_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_7_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_7_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_2 = cert30_layer_7_31_2 := by
  decide

def cert30_seen_7_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_7_31_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_7_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_3 = cert30_layer_7_31_3 := by
  decide

def cert30_seen_7_31_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_7_31_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_7_31_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_4 = cert30_layer_7_31_4 := by
  decide

def cert30_seen_7_31_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_7_31_5 : List ChainEdge :=
  []

theorem cert30_layer_7_31_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 7 [])
      LColor.b LColor.p cert30_seen_7_31_5 = cert30_layer_7_31_5 := by
  decide

theorem cert30_component_7_31_eq :
    closedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_7_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 27 cert30_seen_7_31_0 = cert30_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_0 cert30_layer_7_31_0 26 cert30_layer_7_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 26 cert30_seen_7_31_1 = cert30_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_1 cert30_layer_7_31_1 25 cert30_layer_7_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 25 cert30_seen_7_31_2 = cert30_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_2 cert30_layer_7_31_2 24 cert30_layer_7_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 24 cert30_seen_7_31_3 = cert30_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_3 cert30_layer_7_31_3 23 cert30_layer_7_31_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 23 cert30_seen_7_31_4 = cert30_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_4 cert30_layer_7_31_4 22 cert30_layer_7_31_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 7 [])
      LColor.b LColor.p 22 cert30_seen_7_31_5 = cert30_component_7_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 7 []) LColor.b LColor.p
    cert30_seen_7_31_5 cert30_layer_7_31_5_eq 22

theorem cert30_step_7_31 :
    closedCollarIndexStepBool word fiber30 7 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_7_31)
    (by decide) (by decide)
    (by simpa [cert30_move_7_31] using cert30_component_7_31_eq)
    (by decide) (by decide) (by decide)

def cert30_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_2_0 = cert30_layer_8_2_0 := by
  decide

def cert30_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_8_2_1 : List ChainEdge :=
  []

theorem cert30_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_2_1 = cert30_layer_8_2_1 := by
  decide

theorem cert30_component_8_2_eq :
    closedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 27 cert30_seen_8_2_0 = cert30_component_8_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_2_0 cert30_layer_8_2_0 26 cert30_layer_8_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 26 cert30_seen_8_2_1 = cert30_component_8_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_2_1 cert30_layer_8_2_1_eq 26

theorem cert30_step_8_2 :
    closedCollarIndexStepBool word fiber30 8 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_8_2)
    (by decide) (by decide)
    (by simpa [cert30_move_8_2] using cert30_component_8_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_8_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_8_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_8_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.r LColor.b cert30_seen_8_20_0 = cert30_layer_8_20_0 := by
  decide

def cert30_seen_8_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_8_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_8_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.r LColor.b cert30_seen_8_20_1 = cert30_layer_8_20_1 := by
  decide

def cert30_seen_8_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_8_20_2 : List ChainEdge :=
  []

theorem cert30_layer_8_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.r LColor.b cert30_seen_8_20_2 = cert30_layer_8_20_2 := by
  decide

theorem cert30_component_8_20_eq :
    closedCollarComponent word (listGetD fiber30 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_8_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.r LColor.b 27 cert30_seen_8_20_0 = cert30_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.r LColor.b
    cert30_seen_8_20_0 cert30_layer_8_20_0 26 cert30_layer_8_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.r LColor.b 26 cert30_seen_8_20_1 = cert30_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.r LColor.b
    cert30_seen_8_20_1 cert30_layer_8_20_1 25 cert30_layer_8_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.r LColor.b 25 cert30_seen_8_20_2 = cert30_component_8_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 8 []) LColor.r LColor.b
    cert30_seen_8_20_2 cert30_layer_8_20_2_eq 25

theorem cert30_step_8_20 :
    closedCollarIndexStepBool word fiber30 8 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_8_20)
    (by decide) (by decide)
    (by simpa [cert30_move_8_20] using cert30_component_8_20_eq)
    (by decide) (by decide) (by decide)

def cert30_move_8_32 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_8_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_8_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_32_0 = cert30_layer_8_32_0 := by
  decide

def cert30_seen_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_8_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_32_1 = cert30_layer_8_32_1 := by
  decide

def cert30_seen_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_8_32_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_8_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_32_2 = cert30_layer_8_32_2 := by
  decide

def cert30_seen_8_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_8_32_3 : List ChainEdge :=
  []

theorem cert30_layer_8_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 8 [])
      LColor.b LColor.p cert30_seen_8_32_3 = cert30_layer_8_32_3 := by
  decide

theorem cert30_component_8_32_eq :
    closedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_8_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 27 cert30_seen_8_32_0 = cert30_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_32_0 cert30_layer_8_32_0 26 cert30_layer_8_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 26 cert30_seen_8_32_1 = cert30_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_32_1 cert30_layer_8_32_1 25 cert30_layer_8_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 25 cert30_seen_8_32_2 = cert30_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_32_2 cert30_layer_8_32_2 24 cert30_layer_8_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 8 [])
      LColor.b LColor.p 24 cert30_seen_8_32_3 = cert30_component_8_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 8 []) LColor.b LColor.p
    cert30_seen_8_32_3 cert30_layer_8_32_3_eq 24

theorem cert30_step_8_32 :
    closedCollarIndexStepBool word fiber30 8 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_8_32)
    (by decide) (by decide)
    (by simpa [cert30_move_8_32] using cert30_component_8_32_eq)
    (by decide) (by decide) (by decide)

def cert30_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_3_0 = cert30_layer_9_3_0 := by
  decide

def cert30_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_9_3_1 : List ChainEdge :=
  []

theorem cert30_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_3_1 = cert30_layer_9_3_1 := by
  decide

theorem cert30_component_9_3_eq :
    closedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 27 cert30_seen_9_3_0 = cert30_component_9_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_3_0 cert30_layer_9_3_0 26 cert30_layer_9_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 26 cert30_seen_9_3_1 = cert30_component_9_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_3_1 cert30_layer_9_3_1_eq 26

theorem cert30_step_9_3 :
    closedCollarIndexStepBool word fiber30 9 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_9_3)
    (by decide) (by decide)
    (by simpa [cert30_move_9_3] using cert30_component_9_3_eq)
    (by decide) (by decide) (by decide)

def cert30_move_9_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_9_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_9_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.r LColor.b cert30_seen_9_21_0 = cert30_layer_9_21_0 := by
  decide

def cert30_seen_9_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_9_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_9_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.r LColor.b cert30_seen_9_21_1 = cert30_layer_9_21_1 := by
  decide

def cert30_seen_9_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_9_21_2 : List ChainEdge :=
  []

theorem cert30_layer_9_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.r LColor.b cert30_seen_9_21_2 = cert30_layer_9_21_2 := by
  decide

theorem cert30_component_9_21_eq :
    closedCollarComponent word (listGetD fiber30 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_9_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.r LColor.b 27 cert30_seen_9_21_0 = cert30_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.r LColor.b
    cert30_seen_9_21_0 cert30_layer_9_21_0 26 cert30_layer_9_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.r LColor.b 26 cert30_seen_9_21_1 = cert30_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.r LColor.b
    cert30_seen_9_21_1 cert30_layer_9_21_1 25 cert30_layer_9_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.r LColor.b 25 cert30_seen_9_21_2 = cert30_component_9_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 9 []) LColor.r LColor.b
    cert30_seen_9_21_2 cert30_layer_9_21_2_eq 25

theorem cert30_step_9_21 :
    closedCollarIndexStepBool word fiber30 9 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_9_21)
    (by decide) (by decide)
    (by simpa [cert30_move_9_21] using cert30_component_9_21_eq)
    (by decide) (by decide) (by decide)

def cert30_move_9_33 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_9_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_9_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_33_0 = cert30_layer_9_33_0 := by
  decide

def cert30_seen_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_9_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_33_1 = cert30_layer_9_33_1 := by
  decide

def cert30_seen_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_9_33_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_9_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_33_2 = cert30_layer_9_33_2 := by
  decide

def cert30_seen_9_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_9_33_3 : List ChainEdge :=
  []

theorem cert30_layer_9_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 9 [])
      LColor.b LColor.p cert30_seen_9_33_3 = cert30_layer_9_33_3 := by
  decide

theorem cert30_component_9_33_eq :
    closedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_9_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 27 cert30_seen_9_33_0 = cert30_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_33_0 cert30_layer_9_33_0 26 cert30_layer_9_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 26 cert30_seen_9_33_1 = cert30_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_33_1 cert30_layer_9_33_1 25 cert30_layer_9_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 25 cert30_seen_9_33_2 = cert30_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_33_2 cert30_layer_9_33_2 24 cert30_layer_9_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 9 [])
      LColor.b LColor.p 24 cert30_seen_9_33_3 = cert30_component_9_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 9 []) LColor.b LColor.p
    cert30_seen_9_33_3 cert30_layer_9_33_3_eq 24

theorem cert30_step_9_33 :
    closedCollarIndexStepBool word fiber30 9 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_9_33)
    (by decide) (by decide)
    (by simpa [cert30_move_9_33] using cert30_component_9_33_eq)
    (by decide) (by decide) (by decide)

def cert30_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 10 [])
      LColor.b LColor.p cert30_seen_10_4_0 = cert30_layer_10_4_0 := by
  decide

def cert30_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_10_4_1 : List ChainEdge :=
  []

theorem cert30_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 10 [])
      LColor.b LColor.p cert30_seen_10_4_1 = cert30_layer_10_4_1 := by
  decide

theorem cert30_component_10_4_eq :
    closedCollarComponent word (listGetD fiber30 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 10 [])
      LColor.b LColor.p 27 cert30_seen_10_4_0 = cert30_component_10_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 10 []) LColor.b LColor.p
    cert30_seen_10_4_0 cert30_layer_10_4_0 26 cert30_layer_10_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 10 [])
      LColor.b LColor.p 26 cert30_seen_10_4_1 = cert30_component_10_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 10 []) LColor.b LColor.p
    cert30_seen_10_4_1 cert30_layer_10_4_1_eq 26

theorem cert30_step_10_4 :
    closedCollarIndexStepBool word fiber30 10 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_10_4)
    (by decide) (by decide)
    (by simpa [cert30_move_10_4] using cert30_component_10_4_eq)
    (by decide) (by decide) (by decide)

def cert30_move_10_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_10_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_10_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 10 [])
      LColor.r LColor.b cert30_seen_10_22_0 = cert30_layer_10_22_0 := by
  decide

def cert30_seen_10_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_10_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_10_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 10 [])
      LColor.r LColor.b cert30_seen_10_22_1 = cert30_layer_10_22_1 := by
  decide

def cert30_seen_10_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_10_22_2 : List ChainEdge :=
  []

theorem cert30_layer_10_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 10 [])
      LColor.r LColor.b cert30_seen_10_22_2 = cert30_layer_10_22_2 := by
  decide

theorem cert30_component_10_22_eq :
    closedCollarComponent word (listGetD fiber30 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_10_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 10 [])
      LColor.r LColor.b 27 cert30_seen_10_22_0 = cert30_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 10 []) LColor.r LColor.b
    cert30_seen_10_22_0 cert30_layer_10_22_0 26 cert30_layer_10_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 10 [])
      LColor.r LColor.b 26 cert30_seen_10_22_1 = cert30_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 10 []) LColor.r LColor.b
    cert30_seen_10_22_1 cert30_layer_10_22_1 25 cert30_layer_10_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 10 [])
      LColor.r LColor.b 25 cert30_seen_10_22_2 = cert30_component_10_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 10 []) LColor.r LColor.b
    cert30_seen_10_22_2 cert30_layer_10_22_2_eq 25

theorem cert30_step_10_22 :
    closedCollarIndexStepBool word fiber30 10 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_10_22)
    (by decide) (by decide)
    (by simpa [cert30_move_10_22] using cert30_component_10_22_eq)
    (by decide) (by decide) (by decide)

def cert30_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert30_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert30_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert30_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 11 [])
      LColor.b LColor.p cert30_seen_11_5_0 = cert30_layer_11_5_0 := by
  decide

def cert30_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert30_layer_11_5_1 : List ChainEdge :=
  []

theorem cert30_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 11 [])
      LColor.b LColor.p cert30_seen_11_5_1 = cert30_layer_11_5_1 := by
  decide

theorem cert30_component_11_5_eq :
    closedCollarComponent word (listGetD fiber30 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert30_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 11 [])
      LColor.b LColor.p 27 cert30_seen_11_5_0 = cert30_component_11_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 11 []) LColor.b LColor.p
    cert30_seen_11_5_0 cert30_layer_11_5_0 26 cert30_layer_11_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 11 [])
      LColor.b LColor.p 26 cert30_seen_11_5_1 = cert30_component_11_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 11 []) LColor.b LColor.p
    cert30_seen_11_5_1 cert30_layer_11_5_1_eq 26

theorem cert30_step_11_5 :
    closedCollarIndexStepBool word fiber30 11 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_11_5)
    (by decide) (by decide)
    (by simpa [cert30_move_11_5] using cert30_component_11_5_eq)
    (by decide) (by decide) (by decide)

def cert30_move_12_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_12_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.r LColor.b cert30_seen_12_0_0 = cert30_layer_12_0_0 := by
  decide

def cert30_seen_12_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_12_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_12_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.r LColor.b cert30_seen_12_0_1 = cert30_layer_12_0_1 := by
  decide

def cert30_seen_12_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_12_0_2 : List ChainEdge :=
  []

theorem cert30_layer_12_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.r LColor.b cert30_seen_12_0_2 = cert30_layer_12_0_2 := by
  decide

theorem cert30_component_12_0_eq :
    closedCollarComponent word (listGetD fiber30 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_12_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.r LColor.b 27 cert30_seen_12_0_0 = cert30_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.r LColor.b
    cert30_seen_12_0_0 cert30_layer_12_0_0 26 cert30_layer_12_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.r LColor.b 26 cert30_seen_12_0_1 = cert30_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.r LColor.b
    cert30_seen_12_0_1 cert30_layer_12_0_1 25 cert30_layer_12_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.r LColor.b 25 cert30_seen_12_0_2 = cert30_component_12_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 12 []) LColor.r LColor.b
    cert30_seen_12_0_2 cert30_layer_12_0_2_eq 25

theorem cert30_step_12_0 :
    closedCollarIndexStepBool word fiber30 12 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_12_0)
    (by decide) (by decide)
    (by simpa [cert30_move_12_0] using cert30_component_12_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_12_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_12_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_seen_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_12_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_12_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_0 = cert30_layer_12_36_0 := by
  decide

def cert30_seen_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_12_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_12_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_1 = cert30_layer_12_36_1 := by
  decide

def cert30_seen_12_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_12_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_12_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_2 = cert30_layer_12_36_2 := by
  decide

def cert30_seen_12_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_12_36_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_12_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_3 = cert30_layer_12_36_3 := by
  decide

def cert30_seen_12_36_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_12_36_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_12_36_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_4 = cert30_layer_12_36_4 := by
  decide

def cert30_seen_12_36_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_12_36_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert30_layer_12_36_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_5 = cert30_layer_12_36_5 := by
  decide

def cert30_seen_12_36_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_layer_12_36_6 : List ChainEdge :=
  []

theorem cert30_layer_12_36_6_eq :
    closedCollarComponentLayer word (listGetD fiber30 12 [])
      LColor.b LColor.p cert30_seen_12_36_6 = cert30_layer_12_36_6 := by
  decide

theorem cert30_component_12_36_eq :
    closedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_12_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 27 cert30_seen_12_36_0 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_0 cert30_layer_12_36_0 26 cert30_layer_12_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 26 cert30_seen_12_36_1 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_1 cert30_layer_12_36_1 25 cert30_layer_12_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 25 cert30_seen_12_36_2 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_2 cert30_layer_12_36_2 24 cert30_layer_12_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 24 cert30_seen_12_36_3 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_3 cert30_layer_12_36_3 23 cert30_layer_12_36_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 23 cert30_seen_12_36_4 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_4 cert30_layer_12_36_4 22 cert30_layer_12_36_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 22 cert30_seen_12_36_5 = cert30_component_12_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_5 cert30_layer_12_36_5 21 cert30_layer_12_36_5_eq]
  change closeClosedCollarComponent word (listGetD fiber30 12 [])
      LColor.b LColor.p 21 cert30_seen_12_36_6 = cert30_component_12_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 12 []) LColor.b LColor.p
    cert30_seen_12_36_6 cert30_layer_12_36_6_eq 21

theorem cert30_step_12_36 :
    closedCollarIndexStepBool word fiber30 12 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_12_36)
    (by decide) (by decide)
    (by simpa [cert30_move_12_36] using cert30_component_12_36_eq)
    (by decide) (by decide) (by decide)

def cert30_move_13_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_13_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.r LColor.b cert30_seen_13_1_0 = cert30_layer_13_1_0 := by
  decide

def cert30_seen_13_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_13_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_13_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.r LColor.b cert30_seen_13_1_1 = cert30_layer_13_1_1 := by
  decide

def cert30_seen_13_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_13_1_2 : List ChainEdge :=
  []

theorem cert30_layer_13_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.r LColor.b cert30_seen_13_1_2 = cert30_layer_13_1_2 := by
  decide

theorem cert30_component_13_1_eq :
    closedCollarComponent word (listGetD fiber30 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_13_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.r LColor.b 27 cert30_seen_13_1_0 = cert30_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.r LColor.b
    cert30_seen_13_1_0 cert30_layer_13_1_0 26 cert30_layer_13_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.r LColor.b 26 cert30_seen_13_1_1 = cert30_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.r LColor.b
    cert30_seen_13_1_1 cert30_layer_13_1_1 25 cert30_layer_13_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.r LColor.b 25 cert30_seen_13_1_2 = cert30_component_13_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 13 []) LColor.r LColor.b
    cert30_seen_13_1_2 cert30_layer_13_1_2_eq 25

theorem cert30_step_13_1 :
    closedCollarIndexStepBool word fiber30 13 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_13_1)
    (by decide) (by decide)
    (by simpa [cert30_move_13_1] using cert30_component_13_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_13_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_13_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_seen_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_13_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_13_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_0 = cert30_layer_13_37_0 := by
  decide

def cert30_seen_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_13_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_13_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_1 = cert30_layer_13_37_1 := by
  decide

def cert30_seen_13_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_13_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_13_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_2 = cert30_layer_13_37_2 := by
  decide

def cert30_seen_13_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_13_37_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_13_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_3 = cert30_layer_13_37_3 := by
  decide

def cert30_seen_13_37_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_13_37_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_13_37_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_4 = cert30_layer_13_37_4 := by
  decide

def cert30_seen_13_37_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_13_37_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert30_layer_13_37_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_5 = cert30_layer_13_37_5 := by
  decide

def cert30_seen_13_37_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_layer_13_37_6 : List ChainEdge :=
  []

theorem cert30_layer_13_37_6_eq :
    closedCollarComponentLayer word (listGetD fiber30 13 [])
      LColor.b LColor.p cert30_seen_13_37_6 = cert30_layer_13_37_6 := by
  decide

theorem cert30_component_13_37_eq :
    closedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_13_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 27 cert30_seen_13_37_0 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_0 cert30_layer_13_37_0 26 cert30_layer_13_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 26 cert30_seen_13_37_1 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_1 cert30_layer_13_37_1 25 cert30_layer_13_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 25 cert30_seen_13_37_2 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_2 cert30_layer_13_37_2 24 cert30_layer_13_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 24 cert30_seen_13_37_3 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_3 cert30_layer_13_37_3 23 cert30_layer_13_37_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 23 cert30_seen_13_37_4 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_4 cert30_layer_13_37_4 22 cert30_layer_13_37_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 22 cert30_seen_13_37_5 = cert30_component_13_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_5 cert30_layer_13_37_5 21 cert30_layer_13_37_5_eq]
  change closeClosedCollarComponent word (listGetD fiber30 13 [])
      LColor.b LColor.p 21 cert30_seen_13_37_6 = cert30_component_13_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 13 []) LColor.b LColor.p
    cert30_seen_13_37_6 cert30_layer_13_37_6_eq 21

theorem cert30_step_13_37 :
    closedCollarIndexStepBool word fiber30 13 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_13_37)
    (by decide) (by decide)
    (by simpa [cert30_move_13_37] using cert30_component_13_37_eq)
    (by decide) (by decide) (by decide)

def cert30_move_14_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_14_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.r LColor.b cert30_seen_14_2_0 = cert30_layer_14_2_0 := by
  decide

def cert30_seen_14_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_14_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_14_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.r LColor.b cert30_seen_14_2_1 = cert30_layer_14_2_1 := by
  decide

def cert30_seen_14_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_14_2_2 : List ChainEdge :=
  []

theorem cert30_layer_14_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.r LColor.b cert30_seen_14_2_2 = cert30_layer_14_2_2 := by
  decide

theorem cert30_component_14_2_eq :
    closedCollarComponent word (listGetD fiber30 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_14_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.r LColor.b 27 cert30_seen_14_2_0 = cert30_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.r LColor.b
    cert30_seen_14_2_0 cert30_layer_14_2_0 26 cert30_layer_14_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.r LColor.b 26 cert30_seen_14_2_1 = cert30_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.r LColor.b
    cert30_seen_14_2_1 cert30_layer_14_2_1 25 cert30_layer_14_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.r LColor.b 25 cert30_seen_14_2_2 = cert30_component_14_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 14 []) LColor.r LColor.b
    cert30_seen_14_2_2 cert30_layer_14_2_2_eq 25

theorem cert30_step_14_2 :
    closedCollarIndexStepBool word fiber30 14 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_14_2)
    (by decide) (by decide)
    (by simpa [cert30_move_14_2] using cert30_component_14_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_14_38 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_14_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_14_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_14_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.b LColor.p cert30_seen_14_38_0 = cert30_layer_14_38_0 := by
  decide

def cert30_seen_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_14_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_14_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.b LColor.p cert30_seen_14_38_1 = cert30_layer_14_38_1 := by
  decide

def cert30_seen_14_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_14_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_14_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.b LColor.p cert30_seen_14_38_2 = cert30_layer_14_38_2 := by
  decide

def cert30_seen_14_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_14_38_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_14_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.b LColor.p cert30_seen_14_38_3 = cert30_layer_14_38_3 := by
  decide

def cert30_seen_14_38_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_14_38_4 : List ChainEdge :=
  []

theorem cert30_layer_14_38_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 14 [])
      LColor.b LColor.p cert30_seen_14_38_4 = cert30_layer_14_38_4 := by
  decide

theorem cert30_component_14_38_eq :
    closedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_14_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p 27 cert30_seen_14_38_0 = cert30_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.b LColor.p
    cert30_seen_14_38_0 cert30_layer_14_38_0 26 cert30_layer_14_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p 26 cert30_seen_14_38_1 = cert30_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.b LColor.p
    cert30_seen_14_38_1 cert30_layer_14_38_1 25 cert30_layer_14_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p 25 cert30_seen_14_38_2 = cert30_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.b LColor.p
    cert30_seen_14_38_2 cert30_layer_14_38_2 24 cert30_layer_14_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p 24 cert30_seen_14_38_3 = cert30_component_14_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 14 []) LColor.b LColor.p
    cert30_seen_14_38_3 cert30_layer_14_38_3 23 cert30_layer_14_38_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 14 [])
      LColor.b LColor.p 23 cert30_seen_14_38_4 = cert30_component_14_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 14 []) LColor.b LColor.p
    cert30_seen_14_38_4 cert30_layer_14_38_4_eq 23

theorem cert30_step_14_38 :
    closedCollarIndexStepBool word fiber30 14 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_14_38)
    (by decide) (by decide)
    (by simpa [cert30_move_14_38] using cert30_component_14_38_eq)
    (by decide) (by decide) (by decide)

def cert30_move_15_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_15_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.r LColor.b cert30_seen_15_3_0 = cert30_layer_15_3_0 := by
  decide

def cert30_seen_15_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_15_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_15_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.r LColor.b cert30_seen_15_3_1 = cert30_layer_15_3_1 := by
  decide

def cert30_seen_15_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_15_3_2 : List ChainEdge :=
  []

theorem cert30_layer_15_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.r LColor.b cert30_seen_15_3_2 = cert30_layer_15_3_2 := by
  decide

theorem cert30_component_15_3_eq :
    closedCollarComponent word (listGetD fiber30 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_15_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.r LColor.b 27 cert30_seen_15_3_0 = cert30_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.r LColor.b
    cert30_seen_15_3_0 cert30_layer_15_3_0 26 cert30_layer_15_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.r LColor.b 26 cert30_seen_15_3_1 = cert30_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.r LColor.b
    cert30_seen_15_3_1 cert30_layer_15_3_1 25 cert30_layer_15_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.r LColor.b 25 cert30_seen_15_3_2 = cert30_component_15_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 15 []) LColor.r LColor.b
    cert30_seen_15_3_2 cert30_layer_15_3_2_eq 25

theorem cert30_step_15_3 :
    closedCollarIndexStepBool word fiber30 15 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_15_3)
    (by decide) (by decide)
    (by simpa [cert30_move_15_3] using cert30_component_15_3_eq)
    (by decide) (by decide) (by decide)

def cert30_move_15_39 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_15_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_15_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_15_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.b LColor.p cert30_seen_15_39_0 = cert30_layer_15_39_0 := by
  decide

def cert30_seen_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_15_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_15_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.b LColor.p cert30_seen_15_39_1 = cert30_layer_15_39_1 := by
  decide

def cert30_seen_15_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_15_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_15_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.b LColor.p cert30_seen_15_39_2 = cert30_layer_15_39_2 := by
  decide

def cert30_seen_15_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_15_39_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_15_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.b LColor.p cert30_seen_15_39_3 = cert30_layer_15_39_3 := by
  decide

def cert30_seen_15_39_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_15_39_4 : List ChainEdge :=
  []

theorem cert30_layer_15_39_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 15 [])
      LColor.b LColor.p cert30_seen_15_39_4 = cert30_layer_15_39_4 := by
  decide

theorem cert30_component_15_39_eq :
    closedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_15_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p 27 cert30_seen_15_39_0 = cert30_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.b LColor.p
    cert30_seen_15_39_0 cert30_layer_15_39_0 26 cert30_layer_15_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p 26 cert30_seen_15_39_1 = cert30_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.b LColor.p
    cert30_seen_15_39_1 cert30_layer_15_39_1 25 cert30_layer_15_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p 25 cert30_seen_15_39_2 = cert30_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.b LColor.p
    cert30_seen_15_39_2 cert30_layer_15_39_2 24 cert30_layer_15_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p 24 cert30_seen_15_39_3 = cert30_component_15_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 15 []) LColor.b LColor.p
    cert30_seen_15_39_3 cert30_layer_15_39_3 23 cert30_layer_15_39_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 15 [])
      LColor.b LColor.p 23 cert30_seen_15_39_4 = cert30_component_15_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 15 []) LColor.b LColor.p
    cert30_seen_15_39_4 cert30_layer_15_39_4_eq 23

theorem cert30_step_15_39 :
    closedCollarIndexStepBool word fiber30 15 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_15_39)
    (by decide) (by decide)
    (by simpa [cert30_move_15_39] using cert30_component_15_39_eq)
    (by decide) (by decide) (by decide)

def cert30_move_16_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_16_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 16 [])
      LColor.r LColor.b cert30_seen_16_4_0 = cert30_layer_16_4_0 := by
  decide

def cert30_seen_16_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_16_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_16_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 16 [])
      LColor.r LColor.b cert30_seen_16_4_1 = cert30_layer_16_4_1 := by
  decide

def cert30_seen_16_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_16_4_2 : List ChainEdge :=
  []

theorem cert30_layer_16_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 16 [])
      LColor.r LColor.b cert30_seen_16_4_2 = cert30_layer_16_4_2 := by
  decide

theorem cert30_component_16_4_eq :
    closedCollarComponent word (listGetD fiber30 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_16_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 16 [])
      LColor.r LColor.b 27 cert30_seen_16_4_0 = cert30_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 16 []) LColor.r LColor.b
    cert30_seen_16_4_0 cert30_layer_16_4_0 26 cert30_layer_16_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 16 [])
      LColor.r LColor.b 26 cert30_seen_16_4_1 = cert30_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 16 []) LColor.r LColor.b
    cert30_seen_16_4_1 cert30_layer_16_4_1 25 cert30_layer_16_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 16 [])
      LColor.r LColor.b 25 cert30_seen_16_4_2 = cert30_component_16_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 16 []) LColor.r LColor.b
    cert30_seen_16_4_2 cert30_layer_16_4_2_eq 25

theorem cert30_step_16_4 :
    closedCollarIndexStepBool word fiber30 16 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_16_4)
    (by decide) (by decide)
    (by simpa [cert30_move_16_4] using cert30_component_16_4_eq)
    (by decide) (by decide) (by decide)

def cert30_move_17_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_17_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 17 [])
      LColor.r LColor.b cert30_seen_17_5_0 = cert30_layer_17_5_0 := by
  decide

def cert30_seen_17_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_17_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_17_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 17 [])
      LColor.r LColor.b cert30_seen_17_5_1 = cert30_layer_17_5_1 := by
  decide

def cert30_seen_17_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_17_5_2 : List ChainEdge :=
  []

theorem cert30_layer_17_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 17 [])
      LColor.r LColor.b cert30_seen_17_5_2 = cert30_layer_17_5_2 := by
  decide

theorem cert30_component_17_5_eq :
    closedCollarComponent word (listGetD fiber30 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_17_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 17 [])
      LColor.r LColor.b 27 cert30_seen_17_5_0 = cert30_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 17 []) LColor.r LColor.b
    cert30_seen_17_5_0 cert30_layer_17_5_0 26 cert30_layer_17_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 17 [])
      LColor.r LColor.b 26 cert30_seen_17_5_1 = cert30_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 17 []) LColor.r LColor.b
    cert30_seen_17_5_1 cert30_layer_17_5_1 25 cert30_layer_17_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 17 [])
      LColor.r LColor.b 25 cert30_seen_17_5_2 = cert30_component_17_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 17 []) LColor.r LColor.b
    cert30_seen_17_5_2 cert30_layer_17_5_2_eq 25

theorem cert30_step_17_5 :
    closedCollarIndexStepBool word fiber30 17 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_17_5)
    (by decide) (by decide)
    (by simpa [cert30_move_17_5] using cert30_component_17_5_eq)
    (by decide) (by decide) (by decide)

def cert30_move_18_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_18_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_18_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 18 [])
      LColor.r LColor.b cert30_seen_18_6_0 = cert30_layer_18_6_0 := by
  decide

def cert30_seen_18_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_18_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_18_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 18 [])
      LColor.r LColor.b cert30_seen_18_6_1 = cert30_layer_18_6_1 := by
  decide

def cert30_seen_18_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_18_6_2 : List ChainEdge :=
  []

theorem cert30_layer_18_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 18 [])
      LColor.r LColor.b cert30_seen_18_6_2 = cert30_layer_18_6_2 := by
  decide

theorem cert30_component_18_6_eq :
    closedCollarComponent word (listGetD fiber30 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_18_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 18 [])
      LColor.r LColor.b 27 cert30_seen_18_6_0 = cert30_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 18 []) LColor.r LColor.b
    cert30_seen_18_6_0 cert30_layer_18_6_0 26 cert30_layer_18_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 18 [])
      LColor.r LColor.b 26 cert30_seen_18_6_1 = cert30_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 18 []) LColor.r LColor.b
    cert30_seen_18_6_1 cert30_layer_18_6_1 25 cert30_layer_18_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 18 [])
      LColor.r LColor.b 25 cert30_seen_18_6_2 = cert30_component_18_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 18 []) LColor.r LColor.b
    cert30_seen_18_6_2 cert30_layer_18_6_2_eq 25

theorem cert30_step_18_6 :
    closedCollarIndexStepBool word fiber30 18 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_18_6)
    (by decide) (by decide)
    (by simpa [cert30_move_18_6] using cert30_component_18_6_eq)
    (by decide) (by decide) (by decide)

def cert30_move_19_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_19_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_19_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 19 [])
      LColor.r LColor.b cert30_seen_19_7_0 = cert30_layer_19_7_0 := by
  decide

def cert30_seen_19_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_19_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_19_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 19 [])
      LColor.r LColor.b cert30_seen_19_7_1 = cert30_layer_19_7_1 := by
  decide

def cert30_seen_19_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_19_7_2 : List ChainEdge :=
  []

theorem cert30_layer_19_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 19 [])
      LColor.r LColor.b cert30_seen_19_7_2 = cert30_layer_19_7_2 := by
  decide

theorem cert30_component_19_7_eq :
    closedCollarComponent word (listGetD fiber30 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_19_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 19 [])
      LColor.r LColor.b 27 cert30_seen_19_7_0 = cert30_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 19 []) LColor.r LColor.b
    cert30_seen_19_7_0 cert30_layer_19_7_0 26 cert30_layer_19_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 19 [])
      LColor.r LColor.b 26 cert30_seen_19_7_1 = cert30_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 19 []) LColor.r LColor.b
    cert30_seen_19_7_1 cert30_layer_19_7_1 25 cert30_layer_19_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 19 [])
      LColor.r LColor.b 25 cert30_seen_19_7_2 = cert30_component_19_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 19 []) LColor.r LColor.b
    cert30_seen_19_7_2 cert30_layer_19_7_2_eq 25

theorem cert30_step_19_7 :
    closedCollarIndexStepBool word fiber30 19 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_19_7)
    (by decide) (by decide)
    (by simpa [cert30_move_19_7] using cert30_component_19_7_eq)
    (by decide) (by decide) (by decide)

def cert30_move_20_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_20_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_20_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 20 [])
      LColor.r LColor.b cert30_seen_20_8_0 = cert30_layer_20_8_0 := by
  decide

def cert30_seen_20_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_20_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_20_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 20 [])
      LColor.r LColor.b cert30_seen_20_8_1 = cert30_layer_20_8_1 := by
  decide

def cert30_seen_20_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_20_8_2 : List ChainEdge :=
  []

theorem cert30_layer_20_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 20 [])
      LColor.r LColor.b cert30_seen_20_8_2 = cert30_layer_20_8_2 := by
  decide

theorem cert30_component_20_8_eq :
    closedCollarComponent word (listGetD fiber30 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_20_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 20 [])
      LColor.r LColor.b 27 cert30_seen_20_8_0 = cert30_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 20 []) LColor.r LColor.b
    cert30_seen_20_8_0 cert30_layer_20_8_0 26 cert30_layer_20_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 20 [])
      LColor.r LColor.b 26 cert30_seen_20_8_1 = cert30_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 20 []) LColor.r LColor.b
    cert30_seen_20_8_1 cert30_layer_20_8_1 25 cert30_layer_20_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 20 [])
      LColor.r LColor.b 25 cert30_seen_20_8_2 = cert30_component_20_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 20 []) LColor.r LColor.b
    cert30_seen_20_8_2 cert30_layer_20_8_2_eq 25

theorem cert30_step_20_8 :
    closedCollarIndexStepBool word fiber30 20 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_20_8)
    (by decide) (by decide)
    (by simpa [cert30_move_20_8] using cert30_component_20_8_eq)
    (by decide) (by decide) (by decide)

def cert30_move_21_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_21_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_21_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 21 [])
      LColor.r LColor.b cert30_seen_21_9_0 = cert30_layer_21_9_0 := by
  decide

def cert30_seen_21_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_21_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_21_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 21 [])
      LColor.r LColor.b cert30_seen_21_9_1 = cert30_layer_21_9_1 := by
  decide

def cert30_seen_21_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_21_9_2 : List ChainEdge :=
  []

theorem cert30_layer_21_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 21 [])
      LColor.r LColor.b cert30_seen_21_9_2 = cert30_layer_21_9_2 := by
  decide

theorem cert30_component_21_9_eq :
    closedCollarComponent word (listGetD fiber30 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_21_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 21 [])
      LColor.r LColor.b 27 cert30_seen_21_9_0 = cert30_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 21 []) LColor.r LColor.b
    cert30_seen_21_9_0 cert30_layer_21_9_0 26 cert30_layer_21_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 21 [])
      LColor.r LColor.b 26 cert30_seen_21_9_1 = cert30_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 21 []) LColor.r LColor.b
    cert30_seen_21_9_1 cert30_layer_21_9_1 25 cert30_layer_21_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 21 [])
      LColor.r LColor.b 25 cert30_seen_21_9_2 = cert30_component_21_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 21 []) LColor.r LColor.b
    cert30_seen_21_9_2 cert30_layer_21_9_2_eq 25

theorem cert30_step_21_9 :
    closedCollarIndexStepBool word fiber30 21 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_21_9)
    (by decide) (by decide)
    (by simpa [cert30_move_21_9] using cert30_component_21_9_eq)
    (by decide) (by decide) (by decide)

def cert30_move_22_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_22_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_22_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 22 [])
      LColor.r LColor.b cert30_seen_22_10_0 = cert30_layer_22_10_0 := by
  decide

def cert30_seen_22_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_22_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_22_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 22 [])
      LColor.r LColor.b cert30_seen_22_10_1 = cert30_layer_22_10_1 := by
  decide

def cert30_seen_22_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_22_10_2 : List ChainEdge :=
  []

theorem cert30_layer_22_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 22 [])
      LColor.r LColor.b cert30_seen_22_10_2 = cert30_layer_22_10_2 := by
  decide

theorem cert30_component_22_10_eq :
    closedCollarComponent word (listGetD fiber30 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert30_component_22_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 22 [])
      LColor.r LColor.b 27 cert30_seen_22_10_0 = cert30_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 22 []) LColor.r LColor.b
    cert30_seen_22_10_0 cert30_layer_22_10_0 26 cert30_layer_22_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 22 [])
      LColor.r LColor.b 26 cert30_seen_22_10_1 = cert30_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 22 []) LColor.r LColor.b
    cert30_seen_22_10_1 cert30_layer_22_10_1 25 cert30_layer_22_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 22 [])
      LColor.r LColor.b 25 cert30_seen_22_10_2 = cert30_component_22_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 22 []) LColor.r LColor.b
    cert30_seen_22_10_2 cert30_layer_22_10_2_eq 25

theorem cert30_step_22_10 :
    closedCollarIndexStepBool word fiber30 22 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_22_10)
    (by decide) (by decide)
    (by simpa [cert30_move_22_10] using cert30_component_22_10_eq)
    (by decide) (by decide) (by decide)

def cert30_move_23_47 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_23_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_23_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_23_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_23_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 23 [])
      LColor.b LColor.p cert30_seen_23_47_0 = cert30_layer_23_47_0 := by
  decide

def cert30_seen_23_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_23_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_23_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 23 [])
      LColor.b LColor.p cert30_seen_23_47_1 = cert30_layer_23_47_1 := by
  decide

def cert30_seen_23_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_23_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_23_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 23 [])
      LColor.b LColor.p cert30_seen_23_47_2 = cert30_layer_23_47_2 := by
  decide

def cert30_seen_23_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_23_47_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_23_47_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 23 [])
      LColor.b LColor.p cert30_seen_23_47_3 = cert30_layer_23_47_3 := by
  decide

def cert30_seen_23_47_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_23_47_4 : List ChainEdge :=
  []

theorem cert30_layer_23_47_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 23 [])
      LColor.b LColor.p cert30_seen_23_47_4 = cert30_layer_23_47_4 := by
  decide

theorem cert30_component_23_47_eq :
    closedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_23_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p 27 cert30_seen_23_47_0 = cert30_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 23 []) LColor.b LColor.p
    cert30_seen_23_47_0 cert30_layer_23_47_0 26 cert30_layer_23_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p 26 cert30_seen_23_47_1 = cert30_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 23 []) LColor.b LColor.p
    cert30_seen_23_47_1 cert30_layer_23_47_1 25 cert30_layer_23_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p 25 cert30_seen_23_47_2 = cert30_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 23 []) LColor.b LColor.p
    cert30_seen_23_47_2 cert30_layer_23_47_2 24 cert30_layer_23_47_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p 24 cert30_seen_23_47_3 = cert30_component_23_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 23 []) LColor.b LColor.p
    cert30_seen_23_47_3 cert30_layer_23_47_3 23 cert30_layer_23_47_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 23 [])
      LColor.b LColor.p 23 cert30_seen_23_47_4 = cert30_component_23_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 23 []) LColor.b LColor.p
    cert30_seen_23_47_4 cert30_layer_23_47_4_eq 23

theorem cert30_step_23_47 :
    closedCollarIndexStepBool word fiber30 23 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_23_47)
    (by decide) (by decide)
    (by simpa [cert30_move_23_47] using cert30_component_23_47_eq)
    (by decide) (by decide) (by decide)

def cert30_move_24_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_24_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_0 = cert30_layer_24_0_0 := by
  decide

def cert30_seen_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_24_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_1 = cert30_layer_24_0_1 := by
  decide

def cert30_seen_24_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_24_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_24_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_2 = cert30_layer_24_0_2 := by
  decide

def cert30_seen_24_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_24_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_24_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_3 = cert30_layer_24_0_3 := by
  decide

def cert30_seen_24_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_24_0_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_24_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_4 = cert30_layer_24_0_4 := by
  decide

def cert30_seen_24_0_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_24_0_5 : List ChainEdge :=
  []

theorem cert30_layer_24_0_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.b LColor.p cert30_seen_24_0_5 = cert30_layer_24_0_5 := by
  decide

theorem cert30_component_24_0_eq :
    closedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_24_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 27 cert30_seen_24_0_0 = cert30_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_0 cert30_layer_24_0_0 26 cert30_layer_24_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 26 cert30_seen_24_0_1 = cert30_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_1 cert30_layer_24_0_1 25 cert30_layer_24_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 25 cert30_seen_24_0_2 = cert30_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_2 cert30_layer_24_0_2 24 cert30_layer_24_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 24 cert30_seen_24_0_3 = cert30_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_3 cert30_layer_24_0_3 23 cert30_layer_24_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 23 cert30_seen_24_0_4 = cert30_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_4 cert30_layer_24_0_4 22 cert30_layer_24_0_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.b LColor.p 22 cert30_seen_24_0_5 = cert30_component_24_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 24 []) LColor.b LColor.p
    cert30_seen_24_0_5 cert30_layer_24_0_5_eq 22

theorem cert30_step_24_0 :
    closedCollarIndexStepBool word fiber30 24 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_24_0)
    (by decide) (by decide)
    (by simpa [cert30_move_24_0] using cert30_component_24_0_eq)
    (by decide) (by decide) (by decide)

def cert30_move_24_29 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_24_29 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_24_29_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_24_29_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_24_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_29_0 = cert30_layer_24_29_0 := by
  decide

def cert30_seen_24_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_24_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_24_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_29_1 = cert30_layer_24_29_1 := by
  decide

def cert30_seen_24_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_24_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_24_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_29_2 = cert30_layer_24_29_2 := by
  decide

def cert30_seen_24_29_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_24_29_3 : List ChainEdge :=
  []

theorem cert30_layer_24_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_29_3 = cert30_layer_24_29_3 := by
  decide

theorem cert30_component_24_29_eq :
    closedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_24_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 24 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 27 cert30_seen_24_29_0 = cert30_component_24_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_29_0 cert30_layer_24_29_0 26 cert30_layer_24_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 26 cert30_seen_24_29_1 = cert30_component_24_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_29_1 cert30_layer_24_29_1 25 cert30_layer_24_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 25 cert30_seen_24_29_2 = cert30_component_24_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_29_2 cert30_layer_24_29_2 24 cert30_layer_24_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 24 cert30_seen_24_29_3 = cert30_component_24_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_29_3 cert30_layer_24_29_3_eq 24

theorem cert30_step_24_29 :
    closedCollarIndexStepBool word fiber30 24 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_24_29)
    (by decide) (by decide)
    (by simpa [cert30_move_24_29] using cert30_component_24_29_eq)
    (by decide) (by decide) (by decide)

def cert30_move_24_42 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_24_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_24_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_24_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_24_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_42_0 = cert30_layer_24_42_0 := by
  decide

def cert30_seen_24_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_24_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_24_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_42_1 = cert30_layer_24_42_1 := by
  decide

def cert30_seen_24_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_24_42_2 : List ChainEdge :=
  []

theorem cert30_layer_24_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 24 [])
      LColor.r LColor.p cert30_seen_24_42_2 = cert30_layer_24_42_2 := by
  decide

theorem cert30_component_24_42_eq :
    closedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_24_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 27 cert30_seen_24_42_0 = cert30_component_24_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_42_0 cert30_layer_24_42_0 26 cert30_layer_24_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 26 cert30_seen_24_42_1 = cert30_component_24_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_42_1 cert30_layer_24_42_1 25 cert30_layer_24_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 24 [])
      LColor.r LColor.p 25 cert30_seen_24_42_2 = cert30_component_24_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 24 []) LColor.r LColor.p
    cert30_seen_24_42_2 cert30_layer_24_42_2_eq 25

theorem cert30_step_24_42 :
    closedCollarIndexStepBool word fiber30 24 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_24_42)
    (by decide) (by decide)
    (by simpa [cert30_move_24_42] using cert30_component_24_42_eq)
    (by decide) (by decide) (by decide)

def cert30_move_25_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_25_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_0 = cert30_layer_25_1_0 := by
  decide

def cert30_seen_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_25_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_1 = cert30_layer_25_1_1 := by
  decide

def cert30_seen_25_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_25_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_25_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_2 = cert30_layer_25_1_2 := by
  decide

def cert30_seen_25_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_25_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_25_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_3 = cert30_layer_25_1_3 := by
  decide

def cert30_seen_25_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_25_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_25_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_4 = cert30_layer_25_1_4 := by
  decide

def cert30_seen_25_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_25_1_5 : List ChainEdge :=
  []

theorem cert30_layer_25_1_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.b LColor.p cert30_seen_25_1_5 = cert30_layer_25_1_5 := by
  decide

theorem cert30_component_25_1_eq :
    closedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_25_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 27 cert30_seen_25_1_0 = cert30_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_0 cert30_layer_25_1_0 26 cert30_layer_25_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 26 cert30_seen_25_1_1 = cert30_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_1 cert30_layer_25_1_1 25 cert30_layer_25_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 25 cert30_seen_25_1_2 = cert30_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_2 cert30_layer_25_1_2 24 cert30_layer_25_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 24 cert30_seen_25_1_3 = cert30_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_3 cert30_layer_25_1_3 23 cert30_layer_25_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 23 cert30_seen_25_1_4 = cert30_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_4 cert30_layer_25_1_4 22 cert30_layer_25_1_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.b LColor.p 22 cert30_seen_25_1_5 = cert30_component_25_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 25 []) LColor.b LColor.p
    cert30_seen_25_1_5 cert30_layer_25_1_5_eq 22

theorem cert30_step_25_1 :
    closedCollarIndexStepBool word fiber30 25 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_25_1)
    (by decide) (by decide)
    (by simpa [cert30_move_25_1] using cert30_component_25_1_eq)
    (by decide) (by decide) (by decide)

def cert30_move_25_28 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_25_28 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_25_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_25_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_25_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_28_0 = cert30_layer_25_28_0 := by
  decide

def cert30_seen_25_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_25_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_25_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_28_1 = cert30_layer_25_28_1 := by
  decide

def cert30_seen_25_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_25_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_25_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_28_2 = cert30_layer_25_28_2 := by
  decide

def cert30_seen_25_28_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_25_28_3 : List ChainEdge :=
  []

theorem cert30_layer_25_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_28_3 = cert30_layer_25_28_3 := by
  decide

theorem cert30_component_25_28_eq :
    closedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_25_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 25 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 27 cert30_seen_25_28_0 = cert30_component_25_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_28_0 cert30_layer_25_28_0 26 cert30_layer_25_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 26 cert30_seen_25_28_1 = cert30_component_25_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_28_1 cert30_layer_25_28_1 25 cert30_layer_25_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 25 cert30_seen_25_28_2 = cert30_component_25_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_28_2 cert30_layer_25_28_2 24 cert30_layer_25_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 24 cert30_seen_25_28_3 = cert30_component_25_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_28_3 cert30_layer_25_28_3_eq 24

theorem cert30_step_25_28 :
    closedCollarIndexStepBool word fiber30 25 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_25_28)
    (by decide) (by decide)
    (by simpa [cert30_move_25_28] using cert30_component_25_28_eq)
    (by decide) (by decide) (by decide)

def cert30_move_25_43 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_25_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_25_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_25_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_25_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_43_0 = cert30_layer_25_43_0 := by
  decide

def cert30_seen_25_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_25_43_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_25_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_43_1 = cert30_layer_25_43_1 := by
  decide

def cert30_seen_25_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_25_43_2 : List ChainEdge :=
  []

theorem cert30_layer_25_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 25 [])
      LColor.r LColor.p cert30_seen_25_43_2 = cert30_layer_25_43_2 := by
  decide

theorem cert30_component_25_43_eq :
    closedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_25_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 27 cert30_seen_25_43_0 = cert30_component_25_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_43_0 cert30_layer_25_43_0 26 cert30_layer_25_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 26 cert30_seen_25_43_1 = cert30_component_25_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_43_1 cert30_layer_25_43_1 25 cert30_layer_25_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 25 [])
      LColor.r LColor.p 25 cert30_seen_25_43_2 = cert30_component_25_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 25 []) LColor.r LColor.p
    cert30_seen_25_43_2 cert30_layer_25_43_2_eq 25

theorem cert30_step_25_43 :
    closedCollarIndexStepBool word fiber30 25 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_25_43)
    (by decide) (by decide)
    (by simpa [cert30_move_25_43] using cert30_component_25_43_eq)
    (by decide) (by decide) (by decide)

def cert30_move_26_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_26_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.b LColor.p cert30_seen_26_2_0 = cert30_layer_26_2_0 := by
  decide

def cert30_seen_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_26_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.b LColor.p cert30_seen_26_2_1 = cert30_layer_26_2_1 := by
  decide

def cert30_seen_26_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_26_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_26_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.b LColor.p cert30_seen_26_2_2 = cert30_layer_26_2_2 := by
  decide

def cert30_seen_26_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_26_2_3 : List ChainEdge :=
  []

theorem cert30_layer_26_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.b LColor.p cert30_seen_26_2_3 = cert30_layer_26_2_3 := by
  decide

theorem cert30_component_26_2_eq :
    closedCollarComponent word (listGetD fiber30 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_26_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.b LColor.p 27 cert30_seen_26_2_0 = cert30_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 26 []) LColor.b LColor.p
    cert30_seen_26_2_0 cert30_layer_26_2_0 26 cert30_layer_26_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.b LColor.p 26 cert30_seen_26_2_1 = cert30_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 26 []) LColor.b LColor.p
    cert30_seen_26_2_1 cert30_layer_26_2_1 25 cert30_layer_26_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.b LColor.p 25 cert30_seen_26_2_2 = cert30_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 26 []) LColor.b LColor.p
    cert30_seen_26_2_2 cert30_layer_26_2_2 24 cert30_layer_26_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.b LColor.p 24 cert30_seen_26_2_3 = cert30_component_26_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 26 []) LColor.b LColor.p
    cert30_seen_26_2_3 cert30_layer_26_2_3_eq 24

theorem cert30_step_26_2 :
    closedCollarIndexStepBool word fiber30 26 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_26_2)
    (by decide) (by decide)
    (by simpa [cert30_move_26_2] using cert30_component_26_2_eq)
    (by decide) (by decide) (by decide)

def cert30_move_26_44 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_26_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_26_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_26_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_26_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.r LColor.p cert30_seen_26_44_0 = cert30_layer_26_44_0 := by
  decide

def cert30_seen_26_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_26_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_26_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.r LColor.p cert30_seen_26_44_1 = cert30_layer_26_44_1 := by
  decide

def cert30_seen_26_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_26_44_2 : List ChainEdge :=
  []

theorem cert30_layer_26_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 26 [])
      LColor.r LColor.p cert30_seen_26_44_2 = cert30_layer_26_44_2 := by
  decide

theorem cert30_component_26_44_eq :
    closedCollarComponent word (listGetD fiber30 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_26_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.r LColor.p 27 cert30_seen_26_44_0 = cert30_component_26_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 26 []) LColor.r LColor.p
    cert30_seen_26_44_0 cert30_layer_26_44_0 26 cert30_layer_26_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.r LColor.p 26 cert30_seen_26_44_1 = cert30_component_26_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 26 []) LColor.r LColor.p
    cert30_seen_26_44_1 cert30_layer_26_44_1 25 cert30_layer_26_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 26 [])
      LColor.r LColor.p 25 cert30_seen_26_44_2 = cert30_component_26_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 26 []) LColor.r LColor.p
    cert30_seen_26_44_2 cert30_layer_26_44_2_eq 25

theorem cert30_step_26_44 :
    closedCollarIndexStepBool word fiber30 26 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_26_44)
    (by decide) (by decide)
    (by simpa [cert30_move_26_44] using cert30_component_26_44_eq)
    (by decide) (by decide) (by decide)

def cert30_move_27_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_27_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.b LColor.p cert30_seen_27_3_0 = cert30_layer_27_3_0 := by
  decide

def cert30_seen_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_27_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.b LColor.p cert30_seen_27_3_1 = cert30_layer_27_3_1 := by
  decide

def cert30_seen_27_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_27_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_27_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.b LColor.p cert30_seen_27_3_2 = cert30_layer_27_3_2 := by
  decide

def cert30_seen_27_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_27_3_3 : List ChainEdge :=
  []

theorem cert30_layer_27_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.b LColor.p cert30_seen_27_3_3 = cert30_layer_27_3_3 := by
  decide

theorem cert30_component_27_3_eq :
    closedCollarComponent word (listGetD fiber30 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_27_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.b LColor.p 27 cert30_seen_27_3_0 = cert30_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 27 []) LColor.b LColor.p
    cert30_seen_27_3_0 cert30_layer_27_3_0 26 cert30_layer_27_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.b LColor.p 26 cert30_seen_27_3_1 = cert30_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 27 []) LColor.b LColor.p
    cert30_seen_27_3_1 cert30_layer_27_3_1 25 cert30_layer_27_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.b LColor.p 25 cert30_seen_27_3_2 = cert30_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 27 []) LColor.b LColor.p
    cert30_seen_27_3_2 cert30_layer_27_3_2 24 cert30_layer_27_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.b LColor.p 24 cert30_seen_27_3_3 = cert30_component_27_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 27 []) LColor.b LColor.p
    cert30_seen_27_3_3 cert30_layer_27_3_3_eq 24

theorem cert30_step_27_3 :
    closedCollarIndexStepBool word fiber30 27 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_27_3)
    (by decide) (by decide)
    (by simpa [cert30_move_27_3] using cert30_component_27_3_eq)
    (by decide) (by decide) (by decide)

def cert30_move_27_45 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_27_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_27_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_27_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_27_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.r LColor.p cert30_seen_27_45_0 = cert30_layer_27_45_0 := by
  decide

def cert30_seen_27_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_27_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_27_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.r LColor.p cert30_seen_27_45_1 = cert30_layer_27_45_1 := by
  decide

def cert30_seen_27_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_27_45_2 : List ChainEdge :=
  []

theorem cert30_layer_27_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 27 [])
      LColor.r LColor.p cert30_seen_27_45_2 = cert30_layer_27_45_2 := by
  decide

theorem cert30_component_27_45_eq :
    closedCollarComponent word (listGetD fiber30 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_27_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.r LColor.p 27 cert30_seen_27_45_0 = cert30_component_27_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 27 []) LColor.r LColor.p
    cert30_seen_27_45_0 cert30_layer_27_45_0 26 cert30_layer_27_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.r LColor.p 26 cert30_seen_27_45_1 = cert30_component_27_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 27 []) LColor.r LColor.p
    cert30_seen_27_45_1 cert30_layer_27_45_1 25 cert30_layer_27_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 27 [])
      LColor.r LColor.p 25 cert30_seen_27_45_2 = cert30_component_27_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 27 []) LColor.r LColor.p
    cert30_seen_27_45_2 cert30_layer_27_45_2_eq 25

theorem cert30_step_27_45 :
    closedCollarIndexStepBool word fiber30 27 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_27_45)
    (by decide) (by decide)
    (by simpa [cert30_move_27_45] using cert30_component_27_45_eq)
    (by decide) (by decide) (by decide)

def cert30_move_28_25 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_28_25 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_28_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_28_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_28_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_25_0 = cert30_layer_28_25_0 := by
  decide

def cert30_seen_28_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_28_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_28_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_25_1 = cert30_layer_28_25_1 := by
  decide

def cert30_seen_28_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_28_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_28_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_25_2 = cert30_layer_28_25_2 := by
  decide

def cert30_seen_28_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_28_25_3 : List ChainEdge :=
  []

theorem cert30_layer_28_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_25_3 = cert30_layer_28_25_3 := by
  decide

theorem cert30_component_28_25_eq :
    closedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_28_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 28 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 27 cert30_seen_28_25_0 = cert30_component_28_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_25_0 cert30_layer_28_25_0 26 cert30_layer_28_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 26 cert30_seen_28_25_1 = cert30_component_28_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_25_1 cert30_layer_28_25_1 25 cert30_layer_28_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 25 cert30_seen_28_25_2 = cert30_component_28_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_25_2 cert30_layer_28_25_2 24 cert30_layer_28_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 24 cert30_seen_28_25_3 = cert30_component_28_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_25_3 cert30_layer_28_25_3_eq 24

theorem cert30_step_28_25 :
    closedCollarIndexStepBool word fiber30 28 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_28_25)
    (by decide) (by decide)
    (by simpa [cert30_move_28_25] using cert30_component_28_25_eq)
    (by decide) (by decide) (by decide)

def cert30_move_28_46 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_28_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_28_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_28_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_28_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_46_0 = cert30_layer_28_46_0 := by
  decide

def cert30_seen_28_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_28_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_28_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_46_1 = cert30_layer_28_46_1 := by
  decide

def cert30_seen_28_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_28_46_2 : List ChainEdge :=
  []

theorem cert30_layer_28_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 28 [])
      LColor.r LColor.p cert30_seen_28_46_2 = cert30_layer_28_46_2 := by
  decide

theorem cert30_component_28_46_eq :
    closedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_28_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 28 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 27 cert30_seen_28_46_0 = cert30_component_28_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_46_0 cert30_layer_28_46_0 26 cert30_layer_28_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 26 cert30_seen_28_46_1 = cert30_component_28_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_46_1 cert30_layer_28_46_1 25 cert30_layer_28_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 28 [])
      LColor.r LColor.p 25 cert30_seen_28_46_2 = cert30_component_28_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 28 []) LColor.r LColor.p
    cert30_seen_28_46_2 cert30_layer_28_46_2_eq 25

theorem cert30_step_28_46 :
    closedCollarIndexStepBool word fiber30 28 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_28_46)
    (by decide) (by decide)
    (by simpa [cert30_move_28_46] using cert30_component_28_46_eq)
    (by decide) (by decide) (by decide)

def cert30_move_29_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_29_24 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_29_24_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_29_24_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_29_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_24_0 = cert30_layer_29_24_0 := by
  decide

def cert30_seen_29_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_29_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_29_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_24_1 = cert30_layer_29_24_1 := by
  decide

def cert30_seen_29_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_29_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_29_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_24_2 = cert30_layer_29_24_2 := by
  decide

def cert30_seen_29_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_29_24_3 : List ChainEdge :=
  []

theorem cert30_layer_29_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_24_3 = cert30_layer_29_24_3 := by
  decide

theorem cert30_component_29_24_eq :
    closedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_29_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 29 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 27 cert30_seen_29_24_0 = cert30_component_29_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_24_0 cert30_layer_29_24_0 26 cert30_layer_29_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 26 cert30_seen_29_24_1 = cert30_component_29_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_24_1 cert30_layer_29_24_1 25 cert30_layer_29_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 25 cert30_seen_29_24_2 = cert30_component_29_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_24_2 cert30_layer_29_24_2 24 cert30_layer_29_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 24 cert30_seen_29_24_3 = cert30_component_29_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_24_3 cert30_layer_29_24_3_eq 24

theorem cert30_step_29_24 :
    closedCollarIndexStepBool word fiber30 29 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_29_24)
    (by decide) (by decide)
    (by simpa [cert30_move_29_24] using cert30_component_29_24_eq)
    (by decide) (by decide) (by decide)

def cert30_move_29_47 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_29_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_29_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_29_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_29_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_47_0 = cert30_layer_29_47_0 := by
  decide

def cert30_seen_29_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_29_47_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_29_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_47_1 = cert30_layer_29_47_1 := by
  decide

def cert30_seen_29_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_29_47_2 : List ChainEdge :=
  []

theorem cert30_layer_29_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 29 [])
      LColor.r LColor.p cert30_seen_29_47_2 = cert30_layer_29_47_2 := by
  decide

theorem cert30_component_29_47_eq :
    closedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_29_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 29 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 27 cert30_seen_29_47_0 = cert30_component_29_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_47_0 cert30_layer_29_47_0 26 cert30_layer_29_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 26 cert30_seen_29_47_1 = cert30_component_29_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_47_1 cert30_layer_29_47_1 25 cert30_layer_29_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 29 [])
      LColor.r LColor.p 25 cert30_seen_29_47_2 = cert30_component_29_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 29 []) LColor.r LColor.p
    cert30_seen_29_47_2 cert30_layer_29_47_2_eq 25

theorem cert30_step_29_47 :
    closedCollarIndexStepBool word fiber30 29 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_29_47)
    (by decide) (by decide)
    (by simpa [cert30_move_29_47] using cert30_component_29_47_eq)
    (by decide) (by decide) (by decide)

def cert30_move_30_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_30_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_30_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_0 = cert30_layer_30_6_0 := by
  decide

def cert30_seen_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_30_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_1 = cert30_layer_30_6_1 := by
  decide

def cert30_seen_30_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_30_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_30_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_2 = cert30_layer_30_6_2 := by
  decide

def cert30_seen_30_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_30_6_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_30_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_3 = cert30_layer_30_6_3 := by
  decide

def cert30_seen_30_6_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_30_6_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_30_6_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_4 = cert30_layer_30_6_4 := by
  decide

def cert30_seen_30_6_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_30_6_5 : List ChainEdge :=
  []

theorem cert30_layer_30_6_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.b LColor.p cert30_seen_30_6_5 = cert30_layer_30_6_5 := by
  decide

theorem cert30_component_30_6_eq :
    closedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_30_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 27 cert30_seen_30_6_0 = cert30_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_0 cert30_layer_30_6_0 26 cert30_layer_30_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 26 cert30_seen_30_6_1 = cert30_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_1 cert30_layer_30_6_1 25 cert30_layer_30_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 25 cert30_seen_30_6_2 = cert30_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_2 cert30_layer_30_6_2 24 cert30_layer_30_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 24 cert30_seen_30_6_3 = cert30_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_3 cert30_layer_30_6_3 23 cert30_layer_30_6_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 23 cert30_seen_30_6_4 = cert30_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_4 cert30_layer_30_6_4 22 cert30_layer_30_6_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.b LColor.p 22 cert30_seen_30_6_5 = cert30_component_30_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 30 []) LColor.b LColor.p
    cert30_seen_30_6_5 cert30_layer_30_6_5_eq 22

theorem cert30_step_30_6 :
    closedCollarIndexStepBool word fiber30 30 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_30_6)
    (by decide) (by decide)
    (by simpa [cert30_move_30_6] using cert30_component_30_6_eq)
    (by decide) (by decide) (by decide)

def cert30_move_30_35 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_30_35 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_30_35_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_30_35_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_30_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.r LColor.p cert30_seen_30_35_0 = cert30_layer_30_35_0 := by
  decide

def cert30_seen_30_35_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_30_35_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_30_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.r LColor.p cert30_seen_30_35_1 = cert30_layer_30_35_1 := by
  decide

def cert30_seen_30_35_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_30_35_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_30_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.r LColor.p cert30_seen_30_35_2 = cert30_layer_30_35_2 := by
  decide

def cert30_seen_30_35_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_30_35_3 : List ChainEdge :=
  []

theorem cert30_layer_30_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 30 [])
      LColor.r LColor.p cert30_seen_30_35_3 = cert30_layer_30_35_3 := by
  decide

theorem cert30_component_30_35_eq :
    closedCollarComponent word (listGetD fiber30 30 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_30_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 30 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.r LColor.p 27 cert30_seen_30_35_0 = cert30_component_30_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.r LColor.p
    cert30_seen_30_35_0 cert30_layer_30_35_0 26 cert30_layer_30_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.r LColor.p 26 cert30_seen_30_35_1 = cert30_component_30_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.r LColor.p
    cert30_seen_30_35_1 cert30_layer_30_35_1 25 cert30_layer_30_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.r LColor.p 25 cert30_seen_30_35_2 = cert30_component_30_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 30 []) LColor.r LColor.p
    cert30_seen_30_35_2 cert30_layer_30_35_2 24 cert30_layer_30_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 30 [])
      LColor.r LColor.p 24 cert30_seen_30_35_3 = cert30_component_30_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 30 []) LColor.r LColor.p
    cert30_seen_30_35_3 cert30_layer_30_35_3_eq 24

theorem cert30_step_30_35 :
    closedCollarIndexStepBool word fiber30 30 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_30_35)
    (by decide) (by decide)
    (by simpa [cert30_move_30_35] using cert30_component_30_35_eq)
    (by decide) (by decide) (by decide)

def cert30_move_31_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_31_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_seen_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_31_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_0 = cert30_layer_31_7_0 := by
  decide

def cert30_seen_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_31_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_1 = cert30_layer_31_7_1 := by
  decide

def cert30_seen_31_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_31_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_31_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_2 = cert30_layer_31_7_2 := by
  decide

def cert30_seen_31_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_31_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_31_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_3 = cert30_layer_31_7_3 := by
  decide

def cert30_seen_31_7_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_31_7_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_31_7_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_4 = cert30_layer_31_7_4 := by
  decide

def cert30_seen_31_7_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_31_7_5 : List ChainEdge :=
  []

theorem cert30_layer_31_7_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.b LColor.p cert30_seen_31_7_5 = cert30_layer_31_7_5 := by
  decide

theorem cert30_component_31_7_eq :
    closedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_31_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 27 cert30_seen_31_7_0 = cert30_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_0 cert30_layer_31_7_0 26 cert30_layer_31_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 26 cert30_seen_31_7_1 = cert30_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_1 cert30_layer_31_7_1 25 cert30_layer_31_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 25 cert30_seen_31_7_2 = cert30_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_2 cert30_layer_31_7_2 24 cert30_layer_31_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 24 cert30_seen_31_7_3 = cert30_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_3 cert30_layer_31_7_3 23 cert30_layer_31_7_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 23 cert30_seen_31_7_4 = cert30_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_4 cert30_layer_31_7_4 22 cert30_layer_31_7_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.b LColor.p 22 cert30_seen_31_7_5 = cert30_component_31_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 31 []) LColor.b LColor.p
    cert30_seen_31_7_5 cert30_layer_31_7_5_eq 22

theorem cert30_step_31_7 :
    closedCollarIndexStepBool word fiber30 31 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_31_7)
    (by decide) (by decide)
    (by simpa [cert30_move_31_7] using cert30_component_31_7_eq)
    (by decide) (by decide) (by decide)

def cert30_move_31_34 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_31_34 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_31_34_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_31_34_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_31_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.r LColor.p cert30_seen_31_34_0 = cert30_layer_31_34_0 := by
  decide

def cert30_seen_31_34_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_31_34_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_31_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.r LColor.p cert30_seen_31_34_1 = cert30_layer_31_34_1 := by
  decide

def cert30_seen_31_34_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_31_34_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_31_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.r LColor.p cert30_seen_31_34_2 = cert30_layer_31_34_2 := by
  decide

def cert30_seen_31_34_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_31_34_3 : List ChainEdge :=
  []

theorem cert30_layer_31_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 31 [])
      LColor.r LColor.p cert30_seen_31_34_3 = cert30_layer_31_34_3 := by
  decide

theorem cert30_component_31_34_eq :
    closedCollarComponent word (listGetD fiber30 31 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_31_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 31 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.r LColor.p 27 cert30_seen_31_34_0 = cert30_component_31_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.r LColor.p
    cert30_seen_31_34_0 cert30_layer_31_34_0 26 cert30_layer_31_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.r LColor.p 26 cert30_seen_31_34_1 = cert30_component_31_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.r LColor.p
    cert30_seen_31_34_1 cert30_layer_31_34_1 25 cert30_layer_31_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.r LColor.p 25 cert30_seen_31_34_2 = cert30_component_31_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 31 []) LColor.r LColor.p
    cert30_seen_31_34_2 cert30_layer_31_34_2 24 cert30_layer_31_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 31 [])
      LColor.r LColor.p 24 cert30_seen_31_34_3 = cert30_component_31_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 31 []) LColor.r LColor.p
    cert30_seen_31_34_3 cert30_layer_31_34_3_eq 24

theorem cert30_step_31_34 :
    closedCollarIndexStepBool word fiber30 31 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_31_34)
    (by decide) (by decide)
    (by simpa [cert30_move_31_34] using cert30_component_31_34_eq)
    (by decide) (by decide) (by decide)

def cert30_move_32_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_32_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_32_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 32 [])
      LColor.b LColor.p cert30_seen_32_8_0 = cert30_layer_32_8_0 := by
  decide

def cert30_seen_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_32_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 32 [])
      LColor.b LColor.p cert30_seen_32_8_1 = cert30_layer_32_8_1 := by
  decide

def cert30_seen_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_32_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_32_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 32 [])
      LColor.b LColor.p cert30_seen_32_8_2 = cert30_layer_32_8_2 := by
  decide

def cert30_seen_32_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_32_8_3 : List ChainEdge :=
  []

theorem cert30_layer_32_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 32 [])
      LColor.b LColor.p cert30_seen_32_8_3 = cert30_layer_32_8_3 := by
  decide

theorem cert30_component_32_8_eq :
    closedCollarComponent word (listGetD fiber30 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_32_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 32 [])
      LColor.b LColor.p 27 cert30_seen_32_8_0 = cert30_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 32 []) LColor.b LColor.p
    cert30_seen_32_8_0 cert30_layer_32_8_0 26 cert30_layer_32_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 32 [])
      LColor.b LColor.p 26 cert30_seen_32_8_1 = cert30_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 32 []) LColor.b LColor.p
    cert30_seen_32_8_1 cert30_layer_32_8_1 25 cert30_layer_32_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 32 [])
      LColor.b LColor.p 25 cert30_seen_32_8_2 = cert30_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 32 []) LColor.b LColor.p
    cert30_seen_32_8_2 cert30_layer_32_8_2 24 cert30_layer_32_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 32 [])
      LColor.b LColor.p 24 cert30_seen_32_8_3 = cert30_component_32_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 32 []) LColor.b LColor.p
    cert30_seen_32_8_3 cert30_layer_32_8_3_eq 24

theorem cert30_step_32_8 :
    closedCollarIndexStepBool word fiber30 32 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_32_8)
    (by decide) (by decide)
    (by simpa [cert30_move_32_8] using cert30_component_32_8_eq)
    (by decide) (by decide) (by decide)

def cert30_move_33_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_33_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_seen_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_33_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 33 [])
      LColor.b LColor.p cert30_seen_33_9_0 = cert30_layer_33_9_0 := by
  decide

def cert30_seen_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_33_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 33 [])
      LColor.b LColor.p cert30_seen_33_9_1 = cert30_layer_33_9_1 := by
  decide

def cert30_seen_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_33_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_33_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 33 [])
      LColor.b LColor.p cert30_seen_33_9_2 = cert30_layer_33_9_2 := by
  decide

def cert30_seen_33_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_33_9_3 : List ChainEdge :=
  []

theorem cert30_layer_33_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 33 [])
      LColor.b LColor.p cert30_seen_33_9_3 = cert30_layer_33_9_3 := by
  decide

theorem cert30_component_33_9_eq :
    closedCollarComponent word (listGetD fiber30 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_33_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 33 [])
      LColor.b LColor.p 27 cert30_seen_33_9_0 = cert30_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 33 []) LColor.b LColor.p
    cert30_seen_33_9_0 cert30_layer_33_9_0 26 cert30_layer_33_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 33 [])
      LColor.b LColor.p 26 cert30_seen_33_9_1 = cert30_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 33 []) LColor.b LColor.p
    cert30_seen_33_9_1 cert30_layer_33_9_1 25 cert30_layer_33_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 33 [])
      LColor.b LColor.p 25 cert30_seen_33_9_2 = cert30_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 33 []) LColor.b LColor.p
    cert30_seen_33_9_2 cert30_layer_33_9_2 24 cert30_layer_33_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 33 [])
      LColor.b LColor.p 24 cert30_seen_33_9_3 = cert30_component_33_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 33 []) LColor.b LColor.p
    cert30_seen_33_9_3 cert30_layer_33_9_3_eq 24

theorem cert30_step_33_9 :
    closedCollarIndexStepBool word fiber30 33 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_33_9)
    (by decide) (by decide)
    (by simpa [cert30_move_33_9] using cert30_component_33_9_eq)
    (by decide) (by decide) (by decide)

def cert30_move_34_31 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_34_31 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_34_31_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_34_31_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_34_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 34 [])
      LColor.r LColor.p cert30_seen_34_31_0 = cert30_layer_34_31_0 := by
  decide

def cert30_seen_34_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_34_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_34_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 34 [])
      LColor.r LColor.p cert30_seen_34_31_1 = cert30_layer_34_31_1 := by
  decide

def cert30_seen_34_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_34_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_34_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 34 [])
      LColor.r LColor.p cert30_seen_34_31_2 = cert30_layer_34_31_2 := by
  decide

def cert30_seen_34_31_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_34_31_3 : List ChainEdge :=
  []

theorem cert30_layer_34_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 34 [])
      LColor.r LColor.p cert30_seen_34_31_3 = cert30_layer_34_31_3 := by
  decide

theorem cert30_component_34_31_eq :
    closedCollarComponent word (listGetD fiber30 34 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_34_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 34 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 34 [])
      LColor.r LColor.p 27 cert30_seen_34_31_0 = cert30_component_34_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 34 []) LColor.r LColor.p
    cert30_seen_34_31_0 cert30_layer_34_31_0 26 cert30_layer_34_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 34 [])
      LColor.r LColor.p 26 cert30_seen_34_31_1 = cert30_component_34_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 34 []) LColor.r LColor.p
    cert30_seen_34_31_1 cert30_layer_34_31_1 25 cert30_layer_34_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 34 [])
      LColor.r LColor.p 25 cert30_seen_34_31_2 = cert30_component_34_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 34 []) LColor.r LColor.p
    cert30_seen_34_31_2 cert30_layer_34_31_2 24 cert30_layer_34_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 34 [])
      LColor.r LColor.p 24 cert30_seen_34_31_3 = cert30_component_34_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 34 []) LColor.r LColor.p
    cert30_seen_34_31_3 cert30_layer_34_31_3_eq 24

theorem cert30_step_34_31 :
    closedCollarIndexStepBool word fiber30 34 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_34_31)
    (by decide) (by decide)
    (by simpa [cert30_move_34_31] using cert30_component_34_31_eq)
    (by decide) (by decide) (by decide)

def cert30_move_35_30 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_35_30 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_35_30_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_35_30_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_35_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 35 [])
      LColor.r LColor.p cert30_seen_35_30_0 = cert30_layer_35_30_0 := by
  decide

def cert30_seen_35_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_35_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_35_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 35 [])
      LColor.r LColor.p cert30_seen_35_30_1 = cert30_layer_35_30_1 := by
  decide

def cert30_seen_35_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_35_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_35_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 35 [])
      LColor.r LColor.p cert30_seen_35_30_2 = cert30_layer_35_30_2 := by
  decide

def cert30_seen_35_30_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_35_30_3 : List ChainEdge :=
  []

theorem cert30_layer_35_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 35 [])
      LColor.r LColor.p cert30_seen_35_30_3 = cert30_layer_35_30_3 := by
  decide

theorem cert30_component_35_30_eq :
    closedCollarComponent word (listGetD fiber30 35 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_35_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 35 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 35 [])
      LColor.r LColor.p 27 cert30_seen_35_30_0 = cert30_component_35_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 35 []) LColor.r LColor.p
    cert30_seen_35_30_0 cert30_layer_35_30_0 26 cert30_layer_35_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 35 [])
      LColor.r LColor.p 26 cert30_seen_35_30_1 = cert30_component_35_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 35 []) LColor.r LColor.p
    cert30_seen_35_30_1 cert30_layer_35_30_1 25 cert30_layer_35_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 35 [])
      LColor.r LColor.p 25 cert30_seen_35_30_2 = cert30_component_35_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 35 []) LColor.r LColor.p
    cert30_seen_35_30_2 cert30_layer_35_30_2 24 cert30_layer_35_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 35 [])
      LColor.r LColor.p 24 cert30_seen_35_30_3 = cert30_component_35_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 35 []) LColor.r LColor.p
    cert30_seen_35_30_3 cert30_layer_35_30_3_eq 24

theorem cert30_step_35_30 :
    closedCollarIndexStepBool word fiber30 35 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_35_30)
    (by decide) (by decide)
    (by simpa [cert30_move_35_30] using cert30_component_35_30_eq)
    (by decide) (by decide) (by decide)

def cert30_move_36_12 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_36_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_seen_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_36_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_36_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_0 = cert30_layer_36_12_0 := by
  decide

def cert30_seen_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_36_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_36_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_1 = cert30_layer_36_12_1 := by
  decide

def cert30_seen_36_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_36_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_36_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_2 = cert30_layer_36_12_2 := by
  decide

def cert30_seen_36_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_36_12_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_36_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_3 = cert30_layer_36_12_3 := by
  decide

def cert30_seen_36_12_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_36_12_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_36_12_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_4 = cert30_layer_36_12_4 := by
  decide

def cert30_seen_36_12_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_36_12_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert30_layer_36_12_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_5 = cert30_layer_36_12_5 := by
  decide

def cert30_seen_36_12_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_layer_36_12_6 : List ChainEdge :=
  []

theorem cert30_layer_36_12_6_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.b LColor.p cert30_seen_36_12_6 = cert30_layer_36_12_6 := by
  decide

theorem cert30_component_36_12_eq :
    closedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_36_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 27 cert30_seen_36_12_0 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_0 cert30_layer_36_12_0 26 cert30_layer_36_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 26 cert30_seen_36_12_1 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_1 cert30_layer_36_12_1 25 cert30_layer_36_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 25 cert30_seen_36_12_2 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_2 cert30_layer_36_12_2 24 cert30_layer_36_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 24 cert30_seen_36_12_3 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_3 cert30_layer_36_12_3 23 cert30_layer_36_12_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 23 cert30_seen_36_12_4 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_4 cert30_layer_36_12_4 22 cert30_layer_36_12_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 22 cert30_seen_36_12_5 = cert30_component_36_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_5 cert30_layer_36_12_5 21 cert30_layer_36_12_5_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.b LColor.p 21 cert30_seen_36_12_6 = cert30_component_36_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 36 []) LColor.b LColor.p
    cert30_seen_36_12_6 cert30_layer_36_12_6_eq 21

theorem cert30_step_36_12 :
    closedCollarIndexStepBool word fiber30 36 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_36_12)
    (by decide) (by decide)
    (by simpa [cert30_move_36_12] using cert30_component_36_12_eq)
    (by decide) (by decide) (by decide)

def cert30_move_36_41 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_36_41 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_36_41_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_36_41_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_36_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.r LColor.p cert30_seen_36_41_0 = cert30_layer_36_41_0 := by
  decide

def cert30_seen_36_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_36_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_36_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.r LColor.p cert30_seen_36_41_1 = cert30_layer_36_41_1 := by
  decide

def cert30_seen_36_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_36_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_36_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.r LColor.p cert30_seen_36_41_2 = cert30_layer_36_41_2 := by
  decide

def cert30_seen_36_41_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_36_41_3 : List ChainEdge :=
  []

theorem cert30_layer_36_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 36 [])
      LColor.r LColor.p cert30_seen_36_41_3 = cert30_layer_36_41_3 := by
  decide

theorem cert30_component_36_41_eq :
    closedCollarComponent word (listGetD fiber30 36 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_36_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 36 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.r LColor.p 27 cert30_seen_36_41_0 = cert30_component_36_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.r LColor.p
    cert30_seen_36_41_0 cert30_layer_36_41_0 26 cert30_layer_36_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.r LColor.p 26 cert30_seen_36_41_1 = cert30_component_36_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.r LColor.p
    cert30_seen_36_41_1 cert30_layer_36_41_1 25 cert30_layer_36_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.r LColor.p 25 cert30_seen_36_41_2 = cert30_component_36_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 36 []) LColor.r LColor.p
    cert30_seen_36_41_2 cert30_layer_36_41_2 24 cert30_layer_36_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 36 [])
      LColor.r LColor.p 24 cert30_seen_36_41_3 = cert30_component_36_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 36 []) LColor.r LColor.p
    cert30_seen_36_41_3 cert30_layer_36_41_3_eq 24

theorem cert30_step_36_41 :
    closedCollarIndexStepBool word fiber30 36 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_36_41)
    (by decide) (by decide)
    (by simpa [cert30_move_36_41] using cert30_component_36_41_eq)
    (by decide) (by decide) (by decide)

def cert30_move_37_13 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_37_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_seen_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_37_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_37_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_0 = cert30_layer_37_13_0 := by
  decide

def cert30_seen_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_37_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_37_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_1 = cert30_layer_37_13_1 := by
  decide

def cert30_seen_37_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_37_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert30_layer_37_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_2 = cert30_layer_37_13_2 := by
  decide

def cert30_seen_37_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert30_layer_37_13_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert30_layer_37_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_3 = cert30_layer_37_13_3 := by
  decide

def cert30_seen_37_13_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert30_layer_37_13_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert30_layer_37_13_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_4 = cert30_layer_37_13_4 := by
  decide

def cert30_seen_37_13_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert30_layer_37_13_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert30_layer_37_13_5_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_5 = cert30_layer_37_13_5 := by
  decide

def cert30_seen_37_13_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert30_layer_37_13_6 : List ChainEdge :=
  []

theorem cert30_layer_37_13_6_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.b LColor.p cert30_seen_37_13_6 = cert30_layer_37_13_6 := by
  decide

theorem cert30_component_37_13_eq :
    closedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_37_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 27 cert30_seen_37_13_0 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_0 cert30_layer_37_13_0 26 cert30_layer_37_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 26 cert30_seen_37_13_1 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_1 cert30_layer_37_13_1 25 cert30_layer_37_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 25 cert30_seen_37_13_2 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_2 cert30_layer_37_13_2 24 cert30_layer_37_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 24 cert30_seen_37_13_3 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_3 cert30_layer_37_13_3 23 cert30_layer_37_13_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 23 cert30_seen_37_13_4 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_4 cert30_layer_37_13_4 22 cert30_layer_37_13_4_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 22 cert30_seen_37_13_5 = cert30_component_37_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_5 cert30_layer_37_13_5 21 cert30_layer_37_13_5_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.b LColor.p 21 cert30_seen_37_13_6 = cert30_component_37_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 37 []) LColor.b LColor.p
    cert30_seen_37_13_6 cert30_layer_37_13_6_eq 21

theorem cert30_step_37_13 :
    closedCollarIndexStepBool word fiber30 37 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_37_13)
    (by decide) (by decide)
    (by simpa [cert30_move_37_13] using cert30_component_37_13_eq)
    (by decide) (by decide) (by decide)

def cert30_move_37_40 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_37_40 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_37_40_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_37_40_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_37_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.r LColor.p cert30_seen_37_40_0 = cert30_layer_37_40_0 := by
  decide

def cert30_seen_37_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_37_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_37_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.r LColor.p cert30_seen_37_40_1 = cert30_layer_37_40_1 := by
  decide

def cert30_seen_37_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_37_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_37_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.r LColor.p cert30_seen_37_40_2 = cert30_layer_37_40_2 := by
  decide

def cert30_seen_37_40_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_37_40_3 : List ChainEdge :=
  []

theorem cert30_layer_37_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 37 [])
      LColor.r LColor.p cert30_seen_37_40_3 = cert30_layer_37_40_3 := by
  decide

theorem cert30_component_37_40_eq :
    closedCollarComponent word (listGetD fiber30 37 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_37_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 37 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.r LColor.p 27 cert30_seen_37_40_0 = cert30_component_37_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.r LColor.p
    cert30_seen_37_40_0 cert30_layer_37_40_0 26 cert30_layer_37_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.r LColor.p 26 cert30_seen_37_40_1 = cert30_component_37_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.r LColor.p
    cert30_seen_37_40_1 cert30_layer_37_40_1 25 cert30_layer_37_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.r LColor.p 25 cert30_seen_37_40_2 = cert30_component_37_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 37 []) LColor.r LColor.p
    cert30_seen_37_40_2 cert30_layer_37_40_2 24 cert30_layer_37_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 37 [])
      LColor.r LColor.p 24 cert30_seen_37_40_3 = cert30_component_37_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 37 []) LColor.r LColor.p
    cert30_seen_37_40_3 cert30_layer_37_40_3_eq 24

theorem cert30_step_37_40 :
    closedCollarIndexStepBool word fiber30 37 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_37_40)
    (by decide) (by decide)
    (by simpa [cert30_move_37_40] using cert30_component_37_40_eq)
    (by decide) (by decide) (by decide)

def cert30_move_38_14 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_38_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_38_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_38_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 38 [])
      LColor.b LColor.p cert30_seen_38_14_0 = cert30_layer_38_14_0 := by
  decide

def cert30_seen_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_38_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_38_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 38 [])
      LColor.b LColor.p cert30_seen_38_14_1 = cert30_layer_38_14_1 := by
  decide

def cert30_seen_38_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_38_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_38_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 38 [])
      LColor.b LColor.p cert30_seen_38_14_2 = cert30_layer_38_14_2 := by
  decide

def cert30_seen_38_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_38_14_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_38_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 38 [])
      LColor.b LColor.p cert30_seen_38_14_3 = cert30_layer_38_14_3 := by
  decide

def cert30_seen_38_14_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_38_14_4 : List ChainEdge :=
  []

theorem cert30_layer_38_14_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 38 [])
      LColor.b LColor.p cert30_seen_38_14_4 = cert30_layer_38_14_4 := by
  decide

theorem cert30_component_38_14_eq :
    closedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_38_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p 27 cert30_seen_38_14_0 = cert30_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 38 []) LColor.b LColor.p
    cert30_seen_38_14_0 cert30_layer_38_14_0 26 cert30_layer_38_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p 26 cert30_seen_38_14_1 = cert30_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 38 []) LColor.b LColor.p
    cert30_seen_38_14_1 cert30_layer_38_14_1 25 cert30_layer_38_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p 25 cert30_seen_38_14_2 = cert30_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 38 []) LColor.b LColor.p
    cert30_seen_38_14_2 cert30_layer_38_14_2 24 cert30_layer_38_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p 24 cert30_seen_38_14_3 = cert30_component_38_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 38 []) LColor.b LColor.p
    cert30_seen_38_14_3 cert30_layer_38_14_3 23 cert30_layer_38_14_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 38 [])
      LColor.b LColor.p 23 cert30_seen_38_14_4 = cert30_component_38_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 38 []) LColor.b LColor.p
    cert30_seen_38_14_4 cert30_layer_38_14_4_eq 23

theorem cert30_step_38_14 :
    closedCollarIndexStepBool word fiber30 38 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_38_14)
    (by decide) (by decide)
    (by simpa [cert30_move_38_14] using cert30_component_38_14_eq)
    (by decide) (by decide) (by decide)

def cert30_move_39_15 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_39_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_39_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_39_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 39 [])
      LColor.b LColor.p cert30_seen_39_15_0 = cert30_layer_39_15_0 := by
  decide

def cert30_seen_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_39_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_39_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 39 [])
      LColor.b LColor.p cert30_seen_39_15_1 = cert30_layer_39_15_1 := by
  decide

def cert30_seen_39_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_39_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_39_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 39 [])
      LColor.b LColor.p cert30_seen_39_15_2 = cert30_layer_39_15_2 := by
  decide

def cert30_seen_39_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_39_15_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_39_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 39 [])
      LColor.b LColor.p cert30_seen_39_15_3 = cert30_layer_39_15_3 := by
  decide

def cert30_seen_39_15_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_39_15_4 : List ChainEdge :=
  []

theorem cert30_layer_39_15_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 39 [])
      LColor.b LColor.p cert30_seen_39_15_4 = cert30_layer_39_15_4 := by
  decide

theorem cert30_component_39_15_eq :
    closedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_39_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p 27 cert30_seen_39_15_0 = cert30_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 39 []) LColor.b LColor.p
    cert30_seen_39_15_0 cert30_layer_39_15_0 26 cert30_layer_39_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p 26 cert30_seen_39_15_1 = cert30_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 39 []) LColor.b LColor.p
    cert30_seen_39_15_1 cert30_layer_39_15_1 25 cert30_layer_39_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p 25 cert30_seen_39_15_2 = cert30_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 39 []) LColor.b LColor.p
    cert30_seen_39_15_2 cert30_layer_39_15_2 24 cert30_layer_39_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p 24 cert30_seen_39_15_3 = cert30_component_39_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 39 []) LColor.b LColor.p
    cert30_seen_39_15_3 cert30_layer_39_15_3 23 cert30_layer_39_15_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 39 [])
      LColor.b LColor.p 23 cert30_seen_39_15_4 = cert30_component_39_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 39 []) LColor.b LColor.p
    cert30_seen_39_15_4 cert30_layer_39_15_4_eq 23

theorem cert30_step_39_15 :
    closedCollarIndexStepBool word fiber30 39 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_39_15)
    (by decide) (by decide)
    (by simpa [cert30_move_39_15] using cert30_component_39_15_eq)
    (by decide) (by decide) (by decide)

def cert30_move_40_37 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_40_37 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_seen_40_37_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_40_37_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_40_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 40 [])
      LColor.r LColor.p cert30_seen_40_37_0 = cert30_layer_40_37_0 := by
  decide

def cert30_seen_40_37_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_40_37_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_40_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 40 [])
      LColor.r LColor.p cert30_seen_40_37_1 = cert30_layer_40_37_1 := by
  decide

def cert30_seen_40_37_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_40_37_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert30_layer_40_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 40 [])
      LColor.r LColor.p cert30_seen_40_37_2 = cert30_layer_40_37_2 := by
  decide

def cert30_seen_40_37_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert30_layer_40_37_3 : List ChainEdge :=
  []

theorem cert30_layer_40_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 40 [])
      LColor.r LColor.p cert30_seen_40_37_3 = cert30_layer_40_37_3 := by
  decide

theorem cert30_component_40_37_eq :
    closedCollarComponent word (listGetD fiber30 40 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_40_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 40 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 40 [])
      LColor.r LColor.p 27 cert30_seen_40_37_0 = cert30_component_40_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 40 []) LColor.r LColor.p
    cert30_seen_40_37_0 cert30_layer_40_37_0 26 cert30_layer_40_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 40 [])
      LColor.r LColor.p 26 cert30_seen_40_37_1 = cert30_component_40_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 40 []) LColor.r LColor.p
    cert30_seen_40_37_1 cert30_layer_40_37_1 25 cert30_layer_40_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 40 [])
      LColor.r LColor.p 25 cert30_seen_40_37_2 = cert30_component_40_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 40 []) LColor.r LColor.p
    cert30_seen_40_37_2 cert30_layer_40_37_2 24 cert30_layer_40_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 40 [])
      LColor.r LColor.p 24 cert30_seen_40_37_3 = cert30_component_40_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 40 []) LColor.r LColor.p
    cert30_seen_40_37_3 cert30_layer_40_37_3_eq 24

theorem cert30_step_40_37 :
    closedCollarIndexStepBool word fiber30 40 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_40_37)
    (by decide) (by decide)
    (by simpa [cert30_move_40_37] using cert30_component_40_37_eq)
    (by decide) (by decide) (by decide)

def cert30_move_41_36 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert30_component_41_36 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_seen_41_36_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_41_36_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert30_layer_41_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 41 [])
      LColor.r LColor.p cert30_seen_41_36_0 = cert30_layer_41_36_0 := by
  decide

def cert30_seen_41_36_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert30_layer_41_36_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert30_layer_41_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 41 [])
      LColor.r LColor.p cert30_seen_41_36_1 = cert30_layer_41_36_1 := by
  decide

def cert30_seen_41_36_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert30_layer_41_36_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert30_layer_41_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 41 [])
      LColor.r LColor.p cert30_seen_41_36_2 = cert30_layer_41_36_2 := by
  decide

def cert30_seen_41_36_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert30_layer_41_36_3 : List ChainEdge :=
  []

theorem cert30_layer_41_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 41 [])
      LColor.r LColor.p cert30_seen_41_36_3 = cert30_layer_41_36_3 := by
  decide

theorem cert30_component_41_36_eq :
    closedCollarComponent word (listGetD fiber30 41 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert30_component_41_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 41 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 41 [])
      LColor.r LColor.p 27 cert30_seen_41_36_0 = cert30_component_41_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 41 []) LColor.r LColor.p
    cert30_seen_41_36_0 cert30_layer_41_36_0 26 cert30_layer_41_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 41 [])
      LColor.r LColor.p 26 cert30_seen_41_36_1 = cert30_component_41_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 41 []) LColor.r LColor.p
    cert30_seen_41_36_1 cert30_layer_41_36_1 25 cert30_layer_41_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 41 [])
      LColor.r LColor.p 25 cert30_seen_41_36_2 = cert30_component_41_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 41 []) LColor.r LColor.p
    cert30_seen_41_36_2 cert30_layer_41_36_2 24 cert30_layer_41_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 41 [])
      LColor.r LColor.p 24 cert30_seen_41_36_3 = cert30_component_41_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 41 []) LColor.r LColor.p
    cert30_seen_41_36_3 cert30_layer_41_36_3_eq 24

theorem cert30_step_41_36 :
    closedCollarIndexStepBool word fiber30 41 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_41_36)
    (by decide) (by decide)
    (by simpa [cert30_move_41_36] using cert30_component_41_36_eq)
    (by decide) (by decide) (by decide)

def cert30_move_42_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_42_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_42_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_42_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_42_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 42 [])
      LColor.r LColor.p cert30_seen_42_24_0 = cert30_layer_42_24_0 := by
  decide

def cert30_seen_42_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_42_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_42_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 42 [])
      LColor.r LColor.p cert30_seen_42_24_1 = cert30_layer_42_24_1 := by
  decide

def cert30_seen_42_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_42_24_2 : List ChainEdge :=
  []

theorem cert30_layer_42_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 42 [])
      LColor.r LColor.p cert30_seen_42_24_2 = cert30_layer_42_24_2 := by
  decide

theorem cert30_component_42_24_eq :
    closedCollarComponent word (listGetD fiber30 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_42_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 42 [])
      LColor.r LColor.p 27 cert30_seen_42_24_0 = cert30_component_42_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 42 []) LColor.r LColor.p
    cert30_seen_42_24_0 cert30_layer_42_24_0 26 cert30_layer_42_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 42 [])
      LColor.r LColor.p 26 cert30_seen_42_24_1 = cert30_component_42_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 42 []) LColor.r LColor.p
    cert30_seen_42_24_1 cert30_layer_42_24_1 25 cert30_layer_42_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 42 [])
      LColor.r LColor.p 25 cert30_seen_42_24_2 = cert30_component_42_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 42 []) LColor.r LColor.p
    cert30_seen_42_24_2 cert30_layer_42_24_2_eq 25

theorem cert30_step_42_24 :
    closedCollarIndexStepBool word fiber30 42 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_42_24)
    (by decide) (by decide)
    (by simpa [cert30_move_42_24] using cert30_component_42_24_eq)
    (by decide) (by decide) (by decide)

def cert30_move_43_25 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_43_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_43_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_43_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_43_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 43 [])
      LColor.r LColor.p cert30_seen_43_25_0 = cert30_layer_43_25_0 := by
  decide

def cert30_seen_43_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_43_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_43_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 43 [])
      LColor.r LColor.p cert30_seen_43_25_1 = cert30_layer_43_25_1 := by
  decide

def cert30_seen_43_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_43_25_2 : List ChainEdge :=
  []

theorem cert30_layer_43_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 43 [])
      LColor.r LColor.p cert30_seen_43_25_2 = cert30_layer_43_25_2 := by
  decide

theorem cert30_component_43_25_eq :
    closedCollarComponent word (listGetD fiber30 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_43_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 43 [])
      LColor.r LColor.p 27 cert30_seen_43_25_0 = cert30_component_43_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 43 []) LColor.r LColor.p
    cert30_seen_43_25_0 cert30_layer_43_25_0 26 cert30_layer_43_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 43 [])
      LColor.r LColor.p 26 cert30_seen_43_25_1 = cert30_component_43_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 43 []) LColor.r LColor.p
    cert30_seen_43_25_1 cert30_layer_43_25_1 25 cert30_layer_43_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 43 [])
      LColor.r LColor.p 25 cert30_seen_43_25_2 = cert30_component_43_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 43 []) LColor.r LColor.p
    cert30_seen_43_25_2 cert30_layer_43_25_2_eq 25

theorem cert30_step_43_25 :
    closedCollarIndexStepBool word fiber30 43 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_43_25)
    (by decide) (by decide)
    (by simpa [cert30_move_43_25] using cert30_component_43_25_eq)
    (by decide) (by decide) (by decide)

def cert30_move_44_26 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_44_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_44_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_44_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_44_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 44 [])
      LColor.r LColor.p cert30_seen_44_26_0 = cert30_layer_44_26_0 := by
  decide

def cert30_seen_44_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_44_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_44_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 44 [])
      LColor.r LColor.p cert30_seen_44_26_1 = cert30_layer_44_26_1 := by
  decide

def cert30_seen_44_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_44_26_2 : List ChainEdge :=
  []

theorem cert30_layer_44_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 44 [])
      LColor.r LColor.p cert30_seen_44_26_2 = cert30_layer_44_26_2 := by
  decide

theorem cert30_component_44_26_eq :
    closedCollarComponent word (listGetD fiber30 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_44_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 44 [])
      LColor.r LColor.p 27 cert30_seen_44_26_0 = cert30_component_44_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 44 []) LColor.r LColor.p
    cert30_seen_44_26_0 cert30_layer_44_26_0 26 cert30_layer_44_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 44 [])
      LColor.r LColor.p 26 cert30_seen_44_26_1 = cert30_component_44_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 44 []) LColor.r LColor.p
    cert30_seen_44_26_1 cert30_layer_44_26_1 25 cert30_layer_44_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 44 [])
      LColor.r LColor.p 25 cert30_seen_44_26_2 = cert30_component_44_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 44 []) LColor.r LColor.p
    cert30_seen_44_26_2 cert30_layer_44_26_2_eq 25

theorem cert30_step_44_26 :
    closedCollarIndexStepBool word fiber30 44 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_44_26)
    (by decide) (by decide)
    (by simpa [cert30_move_44_26] using cert30_component_44_26_eq)
    (by decide) (by decide) (by decide)

def cert30_move_45_27 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_45_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_45_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_45_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_45_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 45 [])
      LColor.r LColor.p cert30_seen_45_27_0 = cert30_layer_45_27_0 := by
  decide

def cert30_seen_45_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_45_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_45_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 45 [])
      LColor.r LColor.p cert30_seen_45_27_1 = cert30_layer_45_27_1 := by
  decide

def cert30_seen_45_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_45_27_2 : List ChainEdge :=
  []

theorem cert30_layer_45_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 45 [])
      LColor.r LColor.p cert30_seen_45_27_2 = cert30_layer_45_27_2 := by
  decide

theorem cert30_component_45_27_eq :
    closedCollarComponent word (listGetD fiber30 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_45_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 45 [])
      LColor.r LColor.p 27 cert30_seen_45_27_0 = cert30_component_45_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 45 []) LColor.r LColor.p
    cert30_seen_45_27_0 cert30_layer_45_27_0 26 cert30_layer_45_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 45 [])
      LColor.r LColor.p 26 cert30_seen_45_27_1 = cert30_component_45_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 45 []) LColor.r LColor.p
    cert30_seen_45_27_1 cert30_layer_45_27_1 25 cert30_layer_45_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 45 [])
      LColor.r LColor.p 25 cert30_seen_45_27_2 = cert30_component_45_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 45 []) LColor.r LColor.p
    cert30_seen_45_27_2 cert30_layer_45_27_2_eq 25

theorem cert30_step_45_27 :
    closedCollarIndexStepBool word fiber30 45 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_45_27)
    (by decide) (by decide)
    (by simpa [cert30_move_45_27] using cert30_component_45_27_eq)
    (by decide) (by decide) (by decide)

def cert30_move_46_28 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_46_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_46_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_46_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_46_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 46 [])
      LColor.r LColor.p cert30_seen_46_28_0 = cert30_layer_46_28_0 := by
  decide

def cert30_seen_46_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_46_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_46_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 46 [])
      LColor.r LColor.p cert30_seen_46_28_1 = cert30_layer_46_28_1 := by
  decide

def cert30_seen_46_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_46_28_2 : List ChainEdge :=
  []

theorem cert30_layer_46_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 46 [])
      LColor.r LColor.p cert30_seen_46_28_2 = cert30_layer_46_28_2 := by
  decide

theorem cert30_component_46_28_eq :
    closedCollarComponent word (listGetD fiber30 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_46_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 46 [])
      LColor.r LColor.p 27 cert30_seen_46_28_0 = cert30_component_46_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 46 []) LColor.r LColor.p
    cert30_seen_46_28_0 cert30_layer_46_28_0 26 cert30_layer_46_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 46 [])
      LColor.r LColor.p 26 cert30_seen_46_28_1 = cert30_component_46_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 46 []) LColor.r LColor.p
    cert30_seen_46_28_1 cert30_layer_46_28_1 25 cert30_layer_46_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 46 [])
      LColor.r LColor.p 25 cert30_seen_46_28_2 = cert30_component_46_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 46 []) LColor.r LColor.p
    cert30_seen_46_28_2 cert30_layer_46_28_2_eq 25

theorem cert30_step_46_28 :
    closedCollarIndexStepBool word fiber30 46 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_46_28)
    (by decide) (by decide)
    (by simpa [cert30_move_46_28] using cert30_component_46_28_eq)
    (by decide) (by decide) (by decide)

def cert30_move_47_23 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert30_component_47_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_47_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert30_layer_47_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert30_layer_47_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.b LColor.p cert30_seen_47_23_0 = cert30_layer_47_23_0 := by
  decide

def cert30_seen_47_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert30_layer_47_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert30_layer_47_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.b LColor.p cert30_seen_47_23_1 = cert30_layer_47_23_1 := by
  decide

def cert30_seen_47_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert30_layer_47_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert30_layer_47_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.b LColor.p cert30_seen_47_23_2 = cert30_layer_47_23_2 := by
  decide

def cert30_seen_47_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert30_layer_47_23_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_47_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.b LColor.p cert30_seen_47_23_3 = cert30_layer_47_23_3 := by
  decide

def cert30_seen_47_23_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_47_23_4 : List ChainEdge :=
  []

theorem cert30_layer_47_23_4_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.b LColor.p cert30_seen_47_23_4 = cert30_layer_47_23_4 := by
  decide

theorem cert30_component_47_23_eq :
    closedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert30_component_47_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p 27 cert30_seen_47_23_0 = cert30_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.b LColor.p
    cert30_seen_47_23_0 cert30_layer_47_23_0 26 cert30_layer_47_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p 26 cert30_seen_47_23_1 = cert30_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.b LColor.p
    cert30_seen_47_23_1 cert30_layer_47_23_1 25 cert30_layer_47_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p 25 cert30_seen_47_23_2 = cert30_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.b LColor.p
    cert30_seen_47_23_2 cert30_layer_47_23_2 24 cert30_layer_47_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p 24 cert30_seen_47_23_3 = cert30_component_47_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.b LColor.p
    cert30_seen_47_23_3 cert30_layer_47_23_3 23 cert30_layer_47_23_3_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.b LColor.p 23 cert30_seen_47_23_4 = cert30_component_47_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 47 []) LColor.b LColor.p
    cert30_seen_47_23_4 cert30_layer_47_23_4_eq 23

theorem cert30_step_47_23 :
    closedCollarIndexStepBool word fiber30 47 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_47_23)
    (by decide) (by decide)
    (by simpa [cert30_move_47_23] using cert30_component_47_23_eq)
    (by decide) (by decide) (by decide)

def cert30_move_47_29 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert30_component_47_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_seen_47_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert30_layer_47_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert30_layer_47_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.r LColor.p cert30_seen_47_29_0 = cert30_layer_47_29_0 := by
  decide

def cert30_seen_47_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert30_layer_47_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert30_layer_47_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.r LColor.p cert30_seen_47_29_1 = cert30_layer_47_29_1 := by
  decide

def cert30_seen_47_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert30_layer_47_29_2 : List ChainEdge :=
  []

theorem cert30_layer_47_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber30 47 [])
      LColor.r LColor.p cert30_seen_47_29_2 = cert30_layer_47_29_2 := by
  decide

theorem cert30_component_47_29_eq :
    closedCollarComponent word (listGetD fiber30 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert30_component_47_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber30 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.r LColor.p 27 cert30_seen_47_29_0 = cert30_component_47_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.r LColor.p
    cert30_seen_47_29_0 cert30_layer_47_29_0 26 cert30_layer_47_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.r LColor.p 26 cert30_seen_47_29_1 = cert30_component_47_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber30 47 []) LColor.r LColor.p
    cert30_seen_47_29_1 cert30_layer_47_29_1 25 cert30_layer_47_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber30 47 [])
      LColor.r LColor.p 25 cert30_seen_47_29_2 = cert30_component_47_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber30 47 []) LColor.r LColor.p
    cert30_seen_47_29_2 cert30_layer_47_29_2_eq 25

theorem cert30_step_47_29 :
    closedCollarIndexStepBool word fiber30 47 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert30_move_47_29)
    (by decide) (by decide)
    (by simpa [cert30_move_47_29] using cert30_component_47_29_eq)
    (by decide) (by decide) (by decide)

theorem cert30_row_0 :
    closedCollarParentIndexValid word fiber30 cert30.parents 0 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length]

theorem cert30_row_1 :
    closedCollarParentIndexValid word fiber30 cert30.parents 1 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_1_0, cert30_step_0_1]

theorem cert30_row_2 :
    closedCollarParentIndexValid word fiber30 cert30.parents 2 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_2_0, cert30_step_0_2]

theorem cert30_row_3 :
    closedCollarParentIndexValid word fiber30 cert30.parents 3 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_3_1, cert30_step_1_3]

theorem cert30_row_4 :
    closedCollarParentIndexValid word fiber30 cert30.parents 4 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_4_2, cert30_step_2_4]

theorem cert30_row_5 :
    closedCollarParentIndexValid word fiber30 cert30.parents 5 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_5_3, cert30_step_3_5]

theorem cert30_row_6 :
    closedCollarParentIndexValid word fiber30 cert30.parents 6 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_6_0, cert30_step_0_6]

theorem cert30_row_7 :
    closedCollarParentIndexValid word fiber30 cert30.parents 7 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_7_1, cert30_step_1_7]

theorem cert30_row_8 :
    closedCollarParentIndexValid word fiber30 cert30.parents 8 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_8_2, cert30_step_2_8]

theorem cert30_row_9 :
    closedCollarParentIndexValid word fiber30 cert30.parents 9 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_9_3, cert30_step_3_9]

theorem cert30_row_10 :
    closedCollarParentIndexValid word fiber30 cert30.parents 10 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_10_4, cert30_step_4_10]

theorem cert30_row_11 :
    closedCollarParentIndexValid word fiber30 cert30.parents 11 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_11_5, cert30_step_5_11]

theorem cert30_row_12 :
    closedCollarParentIndexValid word fiber30 cert30.parents 12 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_12_0, cert30_step_0_12]

theorem cert30_row_13 :
    closedCollarParentIndexValid word fiber30 cert30.parents 13 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_13_1, cert30_step_1_13]

theorem cert30_row_14 :
    closedCollarParentIndexValid word fiber30 cert30.parents 14 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_14_2, cert30_step_2_14]

theorem cert30_row_15 :
    closedCollarParentIndexValid word fiber30 cert30.parents 15 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_15_3, cert30_step_3_15]

theorem cert30_row_16 :
    closedCollarParentIndexValid word fiber30 cert30.parents 16 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_16_4, cert30_step_4_16]

theorem cert30_row_17 :
    closedCollarParentIndexValid word fiber30 cert30.parents 17 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_17_5, cert30_step_5_17]

theorem cert30_row_18 :
    closedCollarParentIndexValid word fiber30 cert30.parents 18 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_18_6, cert30_step_6_18]

theorem cert30_row_19 :
    closedCollarParentIndexValid word fiber30 cert30.parents 19 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_19_7, cert30_step_7_19]

theorem cert30_row_20 :
    closedCollarParentIndexValid word fiber30 cert30.parents 20 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_20_8, cert30_step_8_20]

theorem cert30_row_21 :
    closedCollarParentIndexValid word fiber30 cert30.parents 21 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_21_9, cert30_step_9_21]

theorem cert30_row_22 :
    closedCollarParentIndexValid word fiber30 cert30.parents 22 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_22_10, cert30_step_10_22]

theorem cert30_row_23 :
    closedCollarParentIndexValid word fiber30 cert30.parents 23 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_23_47, cert30_step_47_23]

theorem cert30_row_24 :
    closedCollarParentIndexValid word fiber30 cert30.parents 24 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_24_0, cert30_step_0_24]

theorem cert30_row_25 :
    closedCollarParentIndexValid word fiber30 cert30.parents 25 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_25_1, cert30_step_1_25]

theorem cert30_row_26 :
    closedCollarParentIndexValid word fiber30 cert30.parents 26 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_26_2, cert30_step_2_26]

theorem cert30_row_27 :
    closedCollarParentIndexValid word fiber30 cert30.parents 27 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_27_3, cert30_step_3_27]

theorem cert30_row_28 :
    closedCollarParentIndexValid word fiber30 cert30.parents 28 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_28_25, cert30_step_25_28]

theorem cert30_row_29 :
    closedCollarParentIndexValid word fiber30 cert30.parents 29 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_29_24, cert30_step_24_29]

theorem cert30_row_30 :
    closedCollarParentIndexValid word fiber30 cert30.parents 30 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_30_6, cert30_step_6_30]

theorem cert30_row_31 :
    closedCollarParentIndexValid word fiber30 cert30.parents 31 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_31_7, cert30_step_7_31]

theorem cert30_row_32 :
    closedCollarParentIndexValid word fiber30 cert30.parents 32 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_32_8, cert30_step_8_32]

theorem cert30_row_33 :
    closedCollarParentIndexValid word fiber30 cert30.parents 33 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_33_9, cert30_step_9_33]

theorem cert30_row_34 :
    closedCollarParentIndexValid word fiber30 cert30.parents 34 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_34_31, cert30_step_31_34]

theorem cert30_row_35 :
    closedCollarParentIndexValid word fiber30 cert30.parents 35 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_35_30, cert30_step_30_35]

theorem cert30_row_36 :
    closedCollarParentIndexValid word fiber30 cert30.parents 36 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_36_12, cert30_step_12_36]

theorem cert30_row_37 :
    closedCollarParentIndexValid word fiber30 cert30.parents 37 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_37_13, cert30_step_13_37]

theorem cert30_row_38 :
    closedCollarParentIndexValid word fiber30 cert30.parents 38 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_38_14, cert30_step_14_38]

theorem cert30_row_39 :
    closedCollarParentIndexValid word fiber30 cert30.parents 39 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_39_15, cert30_step_15_39]

theorem cert30_row_40 :
    closedCollarParentIndexValid word fiber30 cert30.parents 40 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_40_37, cert30_step_37_40]

theorem cert30_row_41 :
    closedCollarParentIndexValid word fiber30 cert30.parents 41 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_41_36, cert30_step_36_41]

theorem cert30_row_42 :
    closedCollarParentIndexValid word fiber30 cert30.parents 42 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_42_24, cert30_step_24_42]

theorem cert30_row_43 :
    closedCollarParentIndexValid word fiber30 cert30.parents 43 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_43_25, cert30_step_25_43]

theorem cert30_row_44 :
    closedCollarParentIndexValid word fiber30 cert30.parents 44 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_44_26, cert30_step_26_44]

theorem cert30_row_45 :
    closedCollarParentIndexValid word fiber30 cert30.parents 45 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_45_27, cert30_step_27_45]

theorem cert30_row_46 :
    closedCollarParentIndexValid word fiber30 cert30.parents 46 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_46_28, cert30_step_28_46]

theorem cert30_row_47 :
    closedCollarParentIndexValid word fiber30 cert30.parents 47 = true := by
  have cert30_fiber_length : fiber30.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert30, listGetD, cert30_fiber_length, cert30_step_47_29, cert30_step_29_47]

theorem cert30_rows :
    closedCollarSpineRowsValid word fiber30 cert30.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert30_fiber_length : fiber30.length = 48 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert30_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert30_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert30_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert30_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert30_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert30_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert30_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert30_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert30_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert30_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert30_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert30_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert30_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert30_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert30_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert30_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert30_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert30_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert30_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert30_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert30_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert30_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert30_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert30_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert30_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert30_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert30_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert30_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert30_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert30_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert30_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert30_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert30_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert30_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert30_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert30_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert30_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert30_row_43
  by_cases h44 : idx = 44
  · subst idx
    exact cert30_row_44
  by_cases h45 : idx = 45
  · subst idx
    exact cert30_row_45
  by_cases h46 : idx = 46
  · subst idx
    exact cert30_row_46
  by_cases h47 : idx = 47
  · subst idx
    exact cert30_row_47
  · omega

theorem cert30_root :
    closedCollarSpineParentsReachRoot fiber30 cert30 = true := by
  decide

theorem cert30_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.r] := by
  change closedCollarFiberKempeConnected word cert30.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert30 fiber30_eq cert30_rows cert30_root


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
