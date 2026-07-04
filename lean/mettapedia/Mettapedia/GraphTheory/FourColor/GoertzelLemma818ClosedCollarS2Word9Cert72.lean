import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast72 : List TauState :=
  [stateAt 100, stateAt 108, stateAt 116, stateAt 124, stateAt 164, stateAt 172, stateAt 180, stateAt 188]

theorem keyedLast72_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.r, LColor.r]) =
      keyedLast72 := by
  decide

def fiber72OuterChunks : List (List (List TauState)) :=
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
  [stateAt 132, stateAt 88, stateAt 172]
, [stateAt 132, stateAt 89, stateAt 164]
, [stateAt 132, stateAt 90, stateAt 188]
, [stateAt 132, stateAt 91, stateAt 180]
, [stateAt 133, stateAt 80, stateAt 172]
, [stateAt 133, stateAt 81, stateAt 164]
, [stateAt 133, stateAt 82, stateAt 188]
, [stateAt 133, stateAt 83, stateAt 180]
, [stateAt 134, stateAt 72, stateAt 172]
, [stateAt 134, stateAt 73, stateAt 164]
, [stateAt 134, stateAt 74, stateAt 188]
, [stateAt 134, stateAt 75, stateAt 180]
, [stateAt 135, stateAt 64, stateAt 172]
, [stateAt 135, stateAt 65, stateAt 164]
, [stateAt 135, stateAt 66, stateAt 188]
, [stateAt 135, stateAt 67, stateAt 180]
]
, []
, []
, [
  [stateAt 180, stateAt 24, stateAt 172]
, [stateAt 180, stateAt 25, stateAt 164]
, [stateAt 180, stateAt 26, stateAt 188]
, [stateAt 180, stateAt 27, stateAt 180]
, [stateAt 180, stateAt 40, stateAt 108]
, [stateAt 180, stateAt 41, stateAt 100]
, [stateAt 180, stateAt 42, stateAt 124]
, [stateAt 180, stateAt 43, stateAt 116]
, [stateAt 181, stateAt 16, stateAt 172]
, [stateAt 181, stateAt 17, stateAt 164]
, [stateAt 181, stateAt 18, stateAt 188]
, [stateAt 181, stateAt 19, stateAt 180]
, [stateAt 181, stateAt 32, stateAt 108]
, [stateAt 181, stateAt 33, stateAt 100]
, [stateAt 181, stateAt 34, stateAt 124]
, [stateAt 181, stateAt 35, stateAt 116]
, [stateAt 182, stateAt 8, stateAt 172]
, [stateAt 182, stateAt 9, stateAt 164]
, [stateAt 182, stateAt 10, stateAt 188]
, [stateAt 182, stateAt 11, stateAt 180]
, [stateAt 182, stateAt 56, stateAt 108]
, [stateAt 182, stateAt 57, stateAt 100]
, [stateAt 182, stateAt 58, stateAt 124]
, [stateAt 182, stateAt 59, stateAt 116]
, [stateAt 183, stateAt 0, stateAt 172]
, [stateAt 183, stateAt 1, stateAt 164]
, [stateAt 183, stateAt 2, stateAt 188]
, [stateAt 183, stateAt 3, stateAt 180]
, [stateAt 183, stateAt 48, stateAt 108]
, [stateAt 183, stateAt 49, stateAt 100]
, [stateAt 183, stateAt 50, stateAt 124]
, [stateAt 183, stateAt 51, stateAt 116]
]
]

def fiber72 : List (List TauState) :=
  fiber72OuterChunks.flatten

theorem fiber72_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 0 []) =
      listGetD fiber72OuterChunks 0 [] := by
  decide

theorem fiber72_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 1 []) =
      listGetD fiber72OuterChunks 1 [] := by
  decide

theorem fiber72_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 2 []) =
      listGetD fiber72OuterChunks 2 [] := by
  decide

theorem fiber72_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 3 []) =
      listGetD fiber72OuterChunks 3 [] := by
  decide

theorem fiber72_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 4 []) =
      listGetD fiber72OuterChunks 4 [] := by
  decide

theorem fiber72_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 5 []) =
      listGetD fiber72OuterChunks 5 [] := by
  decide

theorem fiber72_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 6 []) =
      listGetD fiber72OuterChunks 6 [] := by
  decide

theorem fiber72_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 7 []) =
      listGetD fiber72OuterChunks 7 [] := by
  decide

theorem fiber72_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 8 []) =
      listGetD fiber72OuterChunks 8 [] := by
  decide

theorem fiber72_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 9 []) =
      listGetD fiber72OuterChunks 9 [] := by
  decide

theorem fiber72_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 10 []) =
      listGetD fiber72OuterChunks 10 [] := by
  decide

theorem fiber72_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks 11 []) =
      listGetD fiber72OuterChunks 11 [] := by
  decide

theorem fiber72_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast72
        (listGetD tauStateChunks idx []) =
      listGetD fiber72OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber72_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber72_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber72_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber72_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber72_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber72_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber72_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber72_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber72_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber72_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber72_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber72_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber72_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast72 =
      fiber72 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast72 tauStateChunks fiber72OuterChunks
    tauStateChunks_eq (by rfl) fiber72_outer_get
  simpa [fiber72] using h

theorem fiber72_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.r, LColor.r] = fiber72 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.r, LColor.r] keyedLast72_eq
  exact hfrom.trans fiber72_keyedFrom_eq

theorem fiber72_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.r, LColor.r] = fiber72 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.r, LColor.r]
  exact hfast.trans fiber72_keyed_eq

def cert72 : ClosedCollarSpineCertificate :=
  { key := [LColor.p, LColor.p, LColor.r, LColor.r],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 0, 1, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 0, 1, 2, 3, 16, 17, 18, 20, 4, 5, 6, 7, 24, 25, 26, 28, 16, 17, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 40, 41, 42, 44] }

def cert72_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert72_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert72_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert72_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert72_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_1_0 = cert72_layer_0_1_0 := by
  decide

def cert72_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert72_layer_0_1_1 : List ChainEdge :=
  []

theorem cert72_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_1_1 = cert72_layer_0_1_1 := by
  decide

theorem cert72_component_0_1_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert72_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 27 cert72_seen_0_1_0 = cert72_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_1_0 cert72_layer_0_1_0 26 cert72_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 26 cert72_seen_0_1_1 = cert72_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_1_1 cert72_layer_0_1_1_eq 26

theorem cert72_step_0_1 :
    closedCollarIndexStepBool word fiber72 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_1)
    (by decide) (by decide)
    (by simpa [cert72_move_0_1] using cert72_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_0 = cert72_layer_0_2_0 := by
  decide

def cert72_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_0_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_1 = cert72_layer_0_2_1 := by
  decide

def cert72_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_0_2_2 : List ChainEdge :=
  []

theorem cert72_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_2_2 = cert72_layer_0_2_2 := by
  decide

theorem cert72_component_0_2_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert72_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 27 cert72_seen_0_2_0 = cert72_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_0 cert72_layer_0_2_0 26 cert72_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 26 cert72_seen_0_2_1 = cert72_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_1 cert72_layer_0_2_1 25 cert72_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 25 cert72_seen_0_2_2 = cert72_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_2_2 cert72_layer_0_2_2_eq 25

theorem cert72_step_0_2 :
    closedCollarIndexStepBool word fiber72 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_2)
    (by decide) (by decide)
    (by simpa [cert72_move_0_2] using cert72_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_0_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_0_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_4_0 = cert72_layer_0_4_0 := by
  decide

def cert72_seen_0_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_0_4_1 : List ChainEdge :=
  []

theorem cert72_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.b LColor.p cert72_seen_0_4_1 = cert72_layer_0_4_1 := by
  decide

theorem cert72_component_0_4_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 27 cert72_seen_0_4_0 = cert72_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_4_0 cert72_layer_0_4_0 26 cert72_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.b LColor.p 26 cert72_seen_0_4_1 = cert72_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.b LColor.p
    cert72_seen_0_4_1 cert72_layer_0_4_1_eq 26

theorem cert72_step_0_4 :
    closedCollarIndexStepBool word fiber72 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_4)
    (by decide) (by decide)
    (by simpa [cert72_move_0_4] using cert72_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert72_move_0_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_0_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_0_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.p cert72_seen_0_12_0 = cert72_layer_0_12_0 := by
  decide

def cert72_seen_0_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_0_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_0_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.p cert72_seen_0_12_1 = cert72_layer_0_12_1 := by
  decide

def cert72_seen_0_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_0_12_2 : List ChainEdge :=
  []

theorem cert72_layer_0_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.p cert72_seen_0_12_2 = cert72_layer_0_12_2 := by
  decide

theorem cert72_component_0_12_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_0_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.p 27 cert72_seen_0_12_0 = cert72_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.p
    cert72_seen_0_12_0 cert72_layer_0_12_0 26 cert72_layer_0_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.p 26 cert72_seen_0_12_1 = cert72_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.p
    cert72_seen_0_12_1 cert72_layer_0_12_1 25 cert72_layer_0_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.p 25 cert72_seen_0_12_2 = cert72_component_0_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.r LColor.p
    cert72_seen_0_12_2 cert72_layer_0_12_2_eq 25

theorem cert72_step_0_12 :
    closedCollarIndexStepBool word fiber72 0 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_12)
    (by decide) (by decide)
    (by simpa [cert72_move_0_12] using cert72_component_0_12_eq)
    (by decide) (by decide) (by decide)

def cert72_move_0_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_0_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_0_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_0_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_16_0 = cert72_layer_0_16_0 := by
  decide

def cert72_seen_0_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_0_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_0_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_16_1 = cert72_layer_0_16_1 := by
  decide

def cert72_seen_0_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_0_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_0_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_16_2 = cert72_layer_0_16_2 := by
  decide

def cert72_seen_0_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_0_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_0_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_16_3 = cert72_layer_0_16_3 := by
  decide

def cert72_seen_0_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_0_16_4 : List ChainEdge :=
  []

theorem cert72_layer_0_16_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 0 [])
      LColor.r LColor.b cert72_seen_0_16_4 = cert72_layer_0_16_4 := by
  decide

theorem cert72_component_0_16_eq :
    closedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_0_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 27 cert72_seen_0_16_0 = cert72_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_16_0 cert72_layer_0_16_0 26 cert72_layer_0_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 26 cert72_seen_0_16_1 = cert72_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_16_1 cert72_layer_0_16_1 25 cert72_layer_0_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 25 cert72_seen_0_16_2 = cert72_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_16_2 cert72_layer_0_16_2 24 cert72_layer_0_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 24 cert72_seen_0_16_3 = cert72_component_0_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_16_3 cert72_layer_0_16_3 23 cert72_layer_0_16_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 0 [])
      LColor.r LColor.b 23 cert72_seen_0_16_4 = cert72_component_0_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 0 []) LColor.r LColor.b
    cert72_seen_0_16_4 cert72_layer_0_16_4_eq 23

theorem cert72_step_0_16 :
    closedCollarIndexStepBool word fiber72 0 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_0_16)
    (by decide) (by decide)
    (by simpa [cert72_move_0_16] using cert72_component_0_16_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert72_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert72_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert72_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert72_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_0_0 = cert72_layer_1_0_0 := by
  decide

def cert72_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert72_layer_1_0_1 : List ChainEdge :=
  []

theorem cert72_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_0_1 = cert72_layer_1_0_1 := by
  decide

theorem cert72_component_1_0_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert72_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 27 cert72_seen_1_0_0 = cert72_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_0_0 cert72_layer_1_0_0 26 cert72_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 26 cert72_seen_1_0_1 = cert72_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_0_1 cert72_layer_1_0_1_eq 26

theorem cert72_step_1_0 :
    closedCollarIndexStepBool word fiber72 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_0)
    (by decide) (by decide)
    (by simpa [cert72_move_1_0] using cert72_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_0 = cert72_layer_1_3_0 := by
  decide

def cert72_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_1_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_1 = cert72_layer_1_3_1 := by
  decide

def cert72_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_1_3_2 : List ChainEdge :=
  []

theorem cert72_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_3_2 = cert72_layer_1_3_2 := by
  decide

theorem cert72_component_1_3_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert72_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 27 cert72_seen_1_3_0 = cert72_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_0 cert72_layer_1_3_0 26 cert72_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 26 cert72_seen_1_3_1 = cert72_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_1 cert72_layer_1_3_1 25 cert72_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 25 cert72_seen_1_3_2 = cert72_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_3_2 cert72_layer_1_3_2_eq 25

theorem cert72_step_1_3 :
    closedCollarIndexStepBool word fiber72 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_3)
    (by decide) (by decide)
    (by simpa [cert72_move_1_3] using cert72_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_1_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_1_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_5_0 = cert72_layer_1_5_0 := by
  decide

def cert72_seen_1_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_1_5_1 : List ChainEdge :=
  []

theorem cert72_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.b LColor.p cert72_seen_1_5_1 = cert72_layer_1_5_1 := by
  decide

theorem cert72_component_1_5_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 27 cert72_seen_1_5_0 = cert72_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_5_0 cert72_layer_1_5_0 26 cert72_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.b LColor.p 26 cert72_seen_1_5_1 = cert72_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.b LColor.p
    cert72_seen_1_5_1 cert72_layer_1_5_1_eq 26

theorem cert72_step_1_5 :
    closedCollarIndexStepBool word fiber72 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_5)
    (by decide) (by decide)
    (by simpa [cert72_move_1_5] using cert72_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_1_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_1_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.p cert72_seen_1_13_0 = cert72_layer_1_13_0 := by
  decide

def cert72_seen_1_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_1_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_1_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.p cert72_seen_1_13_1 = cert72_layer_1_13_1 := by
  decide

def cert72_seen_1_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_1_13_2 : List ChainEdge :=
  []

theorem cert72_layer_1_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.p cert72_seen_1_13_2 = cert72_layer_1_13_2 := by
  decide

theorem cert72_component_1_13_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_1_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.p 27 cert72_seen_1_13_0 = cert72_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.p
    cert72_seen_1_13_0 cert72_layer_1_13_0 26 cert72_layer_1_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.p 26 cert72_seen_1_13_1 = cert72_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.p
    cert72_seen_1_13_1 cert72_layer_1_13_1 25 cert72_layer_1_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.p 25 cert72_seen_1_13_2 = cert72_component_1_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.r LColor.p
    cert72_seen_1_13_2 cert72_layer_1_13_2_eq 25

theorem cert72_step_1_13 :
    closedCollarIndexStepBool word fiber72 1 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_13)
    (by decide) (by decide)
    (by simpa [cert72_move_1_13] using cert72_component_1_13_eq)
    (by decide) (by decide) (by decide)

def cert72_move_1_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_1_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_1_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_1_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_17_0 = cert72_layer_1_17_0 := by
  decide

def cert72_seen_1_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_1_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_1_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_17_1 = cert72_layer_1_17_1 := by
  decide

def cert72_seen_1_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_1_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_1_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_17_2 = cert72_layer_1_17_2 := by
  decide

def cert72_seen_1_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_1_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_1_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_17_3 = cert72_layer_1_17_3 := by
  decide

def cert72_seen_1_17_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_1_17_4 : List ChainEdge :=
  []

theorem cert72_layer_1_17_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 1 [])
      LColor.r LColor.b cert72_seen_1_17_4 = cert72_layer_1_17_4 := by
  decide

theorem cert72_component_1_17_eq :
    closedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_1_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 27 cert72_seen_1_17_0 = cert72_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_17_0 cert72_layer_1_17_0 26 cert72_layer_1_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 26 cert72_seen_1_17_1 = cert72_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_17_1 cert72_layer_1_17_1 25 cert72_layer_1_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 25 cert72_seen_1_17_2 = cert72_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_17_2 cert72_layer_1_17_2 24 cert72_layer_1_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 24 cert72_seen_1_17_3 = cert72_component_1_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_17_3 cert72_layer_1_17_3 23 cert72_layer_1_17_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 1 [])
      LColor.r LColor.b 23 cert72_seen_1_17_4 = cert72_component_1_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 1 []) LColor.r LColor.b
    cert72_seen_1_17_4 cert72_layer_1_17_4_eq 23

theorem cert72_step_1_17 :
    closedCollarIndexStepBool word fiber72 1 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_1_17)
    (by decide) (by decide)
    (by simpa [cert72_move_1_17] using cert72_component_1_17_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_0 = cert72_layer_2_0_0 := by
  decide

def cert72_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_2_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_1 = cert72_layer_2_0_1 := by
  decide

def cert72_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_2_0_2 : List ChainEdge :=
  []

theorem cert72_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_0_2 = cert72_layer_2_0_2 := by
  decide

theorem cert72_component_2_0_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert72_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 27 cert72_seen_2_0_0 = cert72_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_0 cert72_layer_2_0_0 26 cert72_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 26 cert72_seen_2_0_1 = cert72_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_1 cert72_layer_2_0_1 25 cert72_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 25 cert72_seen_2_0_2 = cert72_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_0_2 cert72_layer_2_0_2_eq 25

theorem cert72_step_2_0 :
    closedCollarIndexStepBool word fiber72 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_0)
    (by decide) (by decide)
    (by simpa [cert72_move_2_0] using cert72_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_2_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_2_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_2_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_2_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_6_0 = cert72_layer_2_6_0 := by
  decide

def cert72_seen_2_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_2_6_1 : List ChainEdge :=
  []

theorem cert72_layer_2_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.b LColor.p cert72_seen_2_6_1 = cert72_layer_2_6_1 := by
  decide

theorem cert72_component_2_6_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_2_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 27 cert72_seen_2_6_0 = cert72_component_2_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_6_0 cert72_layer_2_6_0 26 cert72_layer_2_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.b LColor.p 26 cert72_seen_2_6_1 = cert72_component_2_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.b LColor.p
    cert72_seen_2_6_1 cert72_layer_2_6_1_eq 26

theorem cert72_step_2_6 :
    closedCollarIndexStepBool word fiber72 2 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_6)
    (by decide) (by decide)
    (by simpa [cert72_move_2_6] using cert72_component_2_6_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_14 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_2_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_2_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.p cert72_seen_2_14_0 = cert72_layer_2_14_0 := by
  decide

def cert72_seen_2_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_2_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_2_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.p cert72_seen_2_14_1 = cert72_layer_2_14_1 := by
  decide

def cert72_seen_2_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_2_14_2 : List ChainEdge :=
  []

theorem cert72_layer_2_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.p cert72_seen_2_14_2 = cert72_layer_2_14_2 := by
  decide

theorem cert72_component_2_14_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_2_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.p 27 cert72_seen_2_14_0 = cert72_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.p
    cert72_seen_2_14_0 cert72_layer_2_14_0 26 cert72_layer_2_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.p 26 cert72_seen_2_14_1 = cert72_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.p
    cert72_seen_2_14_1 cert72_layer_2_14_1 25 cert72_layer_2_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.p 25 cert72_seen_2_14_2 = cert72_component_2_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.r LColor.p
    cert72_seen_2_14_2 cert72_layer_2_14_2_eq 25

theorem cert72_step_2_14 :
    closedCollarIndexStepBool word fiber72 2 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_14)
    (by decide) (by decide)
    (by simpa [cert72_move_2_14] using cert72_component_2_14_eq)
    (by decide) (by decide) (by decide)

def cert72_move_2_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_2_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_2_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_2_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_18_0 = cert72_layer_2_18_0 := by
  decide

def cert72_seen_2_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_2_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_2_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_18_1 = cert72_layer_2_18_1 := by
  decide

def cert72_seen_2_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_2_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_2_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_18_2 = cert72_layer_2_18_2 := by
  decide

def cert72_seen_2_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_2_18_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_2_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_18_3 = cert72_layer_2_18_3 := by
  decide

def cert72_seen_2_18_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_2_18_4 : List ChainEdge :=
  []

theorem cert72_layer_2_18_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 2 [])
      LColor.r LColor.b cert72_seen_2_18_4 = cert72_layer_2_18_4 := by
  decide

theorem cert72_component_2_18_eq :
    closedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_2_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 27 cert72_seen_2_18_0 = cert72_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_18_0 cert72_layer_2_18_0 26 cert72_layer_2_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 26 cert72_seen_2_18_1 = cert72_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_18_1 cert72_layer_2_18_1 25 cert72_layer_2_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 25 cert72_seen_2_18_2 = cert72_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_18_2 cert72_layer_2_18_2 24 cert72_layer_2_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 24 cert72_seen_2_18_3 = cert72_component_2_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_18_3 cert72_layer_2_18_3 23 cert72_layer_2_18_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 2 [])
      LColor.r LColor.b 23 cert72_seen_2_18_4 = cert72_component_2_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 2 []) LColor.r LColor.b
    cert72_seen_2_18_4 cert72_layer_2_18_4_eq 23

theorem cert72_step_2_18 :
    closedCollarIndexStepBool word fiber72 2 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_2_18)
    (by decide) (by decide)
    (by simpa [cert72_move_2_18] using cert72_component_2_18_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_0 = cert72_layer_3_1_0 := by
  decide

def cert72_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_3_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_1 = cert72_layer_3_1_1 := by
  decide

def cert72_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_3_1_2 : List ChainEdge :=
  []

theorem cert72_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_1_2 = cert72_layer_3_1_2 := by
  decide

theorem cert72_component_3_1_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert72_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 27 cert72_seen_3_1_0 = cert72_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_0 cert72_layer_3_1_0 26 cert72_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 26 cert72_seen_3_1_1 = cert72_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_1 cert72_layer_3_1_1 25 cert72_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 25 cert72_seen_3_1_2 = cert72_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_1_2 cert72_layer_3_1_2_eq 25

theorem cert72_step_3_1 :
    closedCollarIndexStepBool word fiber72 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_1)
    (by decide) (by decide)
    (by simpa [cert72_move_3_1] using cert72_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_3_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_3_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_3_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_3_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_7_0 = cert72_layer_3_7_0 := by
  decide

def cert72_seen_3_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_3_7_1 : List ChainEdge :=
  []

theorem cert72_layer_3_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.b LColor.p cert72_seen_3_7_1 = cert72_layer_3_7_1 := by
  decide

theorem cert72_component_3_7_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_3_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 27 cert72_seen_3_7_0 = cert72_component_3_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_7_0 cert72_layer_3_7_0 26 cert72_layer_3_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.b LColor.p 26 cert72_seen_3_7_1 = cert72_component_3_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.b LColor.p
    cert72_seen_3_7_1 cert72_layer_3_7_1_eq 26

theorem cert72_step_3_7 :
    closedCollarIndexStepBool word fiber72 3 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_7)
    (by decide) (by decide)
    (by simpa [cert72_move_3_7] using cert72_component_3_7_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_15 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_3_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_3_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.p cert72_seen_3_15_0 = cert72_layer_3_15_0 := by
  decide

def cert72_seen_3_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_3_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_3_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.p cert72_seen_3_15_1 = cert72_layer_3_15_1 := by
  decide

def cert72_seen_3_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_3_15_2 : List ChainEdge :=
  []

theorem cert72_layer_3_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.p cert72_seen_3_15_2 = cert72_layer_3_15_2 := by
  decide

theorem cert72_component_3_15_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_3_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.p 27 cert72_seen_3_15_0 = cert72_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.p
    cert72_seen_3_15_0 cert72_layer_3_15_0 26 cert72_layer_3_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.p 26 cert72_seen_3_15_1 = cert72_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.p
    cert72_seen_3_15_1 cert72_layer_3_15_1 25 cert72_layer_3_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.p 25 cert72_seen_3_15_2 = cert72_component_3_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.r LColor.p
    cert72_seen_3_15_2 cert72_layer_3_15_2_eq 25

theorem cert72_step_3_15 :
    closedCollarIndexStepBool word fiber72 3 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_15)
    (by decide) (by decide)
    (by simpa [cert72_move_3_15] using cert72_component_3_15_eq)
    (by decide) (by decide) (by decide)

def cert72_move_3_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_3_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_3_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_3_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_19_0 = cert72_layer_3_19_0 := by
  decide

def cert72_seen_3_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_3_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_3_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_19_1 = cert72_layer_3_19_1 := by
  decide

def cert72_seen_3_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_3_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_3_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_19_2 = cert72_layer_3_19_2 := by
  decide

def cert72_seen_3_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_3_19_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_3_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_19_3 = cert72_layer_3_19_3 := by
  decide

def cert72_seen_3_19_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_3_19_4 : List ChainEdge :=
  []

theorem cert72_layer_3_19_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 3 [])
      LColor.r LColor.b cert72_seen_3_19_4 = cert72_layer_3_19_4 := by
  decide

theorem cert72_component_3_19_eq :
    closedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_3_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 27 cert72_seen_3_19_0 = cert72_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_19_0 cert72_layer_3_19_0 26 cert72_layer_3_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 26 cert72_seen_3_19_1 = cert72_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_19_1 cert72_layer_3_19_1 25 cert72_layer_3_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 25 cert72_seen_3_19_2 = cert72_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_19_2 cert72_layer_3_19_2 24 cert72_layer_3_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 24 cert72_seen_3_19_3 = cert72_component_3_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_19_3 cert72_layer_3_19_3 23 cert72_layer_3_19_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 3 [])
      LColor.r LColor.b 23 cert72_seen_3_19_4 = cert72_component_3_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 3 []) LColor.r LColor.b
    cert72_seen_3_19_4 cert72_layer_3_19_4_eq 23

theorem cert72_step_3_19 :
    closedCollarIndexStepBool word fiber72 3 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_3_19)
    (by decide) (by decide)
    (by simpa [cert72_move_3_19] using cert72_component_3_19_eq)
    (by decide) (by decide) (by decide)

def cert72_move_4_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_4_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_0_0 = cert72_layer_4_0_0 := by
  decide

def cert72_seen_4_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_4_0_1 : List ChainEdge :=
  []

theorem cert72_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.b LColor.p cert72_seen_4_0_1 = cert72_layer_4_0_1 := by
  decide

theorem cert72_component_4_0_eq :
    closedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 27 cert72_seen_4_0_0 = cert72_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_0_0 cert72_layer_4_0_0 26 cert72_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.b LColor.p 26 cert72_seen_4_0_1 = cert72_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 4 []) LColor.b LColor.p
    cert72_seen_4_0_1 cert72_layer_4_0_1_eq 26

theorem cert72_step_4_0 :
    closedCollarIndexStepBool word fiber72 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_4_0)
    (by decide) (by decide)
    (by simpa [cert72_move_4_0] using cert72_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_4_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_4_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_4_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_4_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_4_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.p cert72_seen_4_8_0 = cert72_layer_4_8_0 := by
  decide

def cert72_seen_4_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_4_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_4_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.p cert72_seen_4_8_1 = cert72_layer_4_8_1 := by
  decide

def cert72_seen_4_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_4_8_2 : List ChainEdge :=
  []

theorem cert72_layer_4_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.p cert72_seen_4_8_2 = cert72_layer_4_8_2 := by
  decide

theorem cert72_component_4_8_eq :
    closedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_4_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.p 27 cert72_seen_4_8_0 = cert72_component_4_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.p
    cert72_seen_4_8_0 cert72_layer_4_8_0 26 cert72_layer_4_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.p 26 cert72_seen_4_8_1 = cert72_component_4_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.p
    cert72_seen_4_8_1 cert72_layer_4_8_1 25 cert72_layer_4_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.p 25 cert72_seen_4_8_2 = cert72_component_4_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 4 []) LColor.r LColor.p
    cert72_seen_4_8_2 cert72_layer_4_8_2_eq 25

theorem cert72_step_4_8 :
    closedCollarIndexStepBool word fiber72 4 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_4_8)
    (by decide) (by decide)
    (by simpa [cert72_move_4_8] using cert72_component_4_8_eq)
    (by decide) (by decide) (by decide)

def cert72_move_4_24 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_4_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_4_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_4_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_4_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.b cert72_seen_4_24_0 = cert72_layer_4_24_0 := by
  decide

def cert72_seen_4_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_4_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_4_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.b cert72_seen_4_24_1 = cert72_layer_4_24_1 := by
  decide

def cert72_seen_4_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_4_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_4_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.b cert72_seen_4_24_2 = cert72_layer_4_24_2 := by
  decide

def cert72_seen_4_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_4_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_4_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.b cert72_seen_4_24_3 = cert72_layer_4_24_3 := by
  decide

def cert72_seen_4_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_4_24_4 : List ChainEdge :=
  []

theorem cert72_layer_4_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 4 [])
      LColor.r LColor.b cert72_seen_4_24_4 = cert72_layer_4_24_4 := by
  decide

theorem cert72_component_4_24_eq :
    closedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_4_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b 27 cert72_seen_4_24_0 = cert72_component_4_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.b
    cert72_seen_4_24_0 cert72_layer_4_24_0 26 cert72_layer_4_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b 26 cert72_seen_4_24_1 = cert72_component_4_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.b
    cert72_seen_4_24_1 cert72_layer_4_24_1 25 cert72_layer_4_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b 25 cert72_seen_4_24_2 = cert72_component_4_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.b
    cert72_seen_4_24_2 cert72_layer_4_24_2 24 cert72_layer_4_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b 24 cert72_seen_4_24_3 = cert72_component_4_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 4 []) LColor.r LColor.b
    cert72_seen_4_24_3 cert72_layer_4_24_3 23 cert72_layer_4_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 4 [])
      LColor.r LColor.b 23 cert72_seen_4_24_4 = cert72_component_4_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 4 []) LColor.r LColor.b
    cert72_seen_4_24_4 cert72_layer_4_24_4_eq 23

theorem cert72_step_4_24 :
    closedCollarIndexStepBool word fiber72 4 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_4_24)
    (by decide) (by decide)
    (by simpa [cert72_move_4_24] using cert72_component_4_24_eq)
    (by decide) (by decide) (by decide)

def cert72_move_5_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_5_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_1_0 = cert72_layer_5_1_0 := by
  decide

def cert72_seen_5_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_5_1_1 : List ChainEdge :=
  []

theorem cert72_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.b LColor.p cert72_seen_5_1_1 = cert72_layer_5_1_1 := by
  decide

theorem cert72_component_5_1_eq :
    closedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 27 cert72_seen_5_1_0 = cert72_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_1_0 cert72_layer_5_1_0 26 cert72_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.b LColor.p 26 cert72_seen_5_1_1 = cert72_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 5 []) LColor.b LColor.p
    cert72_seen_5_1_1 cert72_layer_5_1_1_eq 26

theorem cert72_step_5_1 :
    closedCollarIndexStepBool word fiber72 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_5_1)
    (by decide) (by decide)
    (by simpa [cert72_move_5_1] using cert72_component_5_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_5_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_5_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_5_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_5_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_5_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.p cert72_seen_5_9_0 = cert72_layer_5_9_0 := by
  decide

def cert72_seen_5_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_5_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_5_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.p cert72_seen_5_9_1 = cert72_layer_5_9_1 := by
  decide

def cert72_seen_5_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_5_9_2 : List ChainEdge :=
  []

theorem cert72_layer_5_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.p cert72_seen_5_9_2 = cert72_layer_5_9_2 := by
  decide

theorem cert72_component_5_9_eq :
    closedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_5_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.p 27 cert72_seen_5_9_0 = cert72_component_5_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.p
    cert72_seen_5_9_0 cert72_layer_5_9_0 26 cert72_layer_5_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.p 26 cert72_seen_5_9_1 = cert72_component_5_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.p
    cert72_seen_5_9_1 cert72_layer_5_9_1 25 cert72_layer_5_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.p 25 cert72_seen_5_9_2 = cert72_component_5_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 5 []) LColor.r LColor.p
    cert72_seen_5_9_2 cert72_layer_5_9_2_eq 25

theorem cert72_step_5_9 :
    closedCollarIndexStepBool word fiber72 5 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_5_9)
    (by decide) (by decide)
    (by simpa [cert72_move_5_9] using cert72_component_5_9_eq)
    (by decide) (by decide) (by decide)

def cert72_move_5_25 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_5_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_5_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_5_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_5_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.b cert72_seen_5_25_0 = cert72_layer_5_25_0 := by
  decide

def cert72_seen_5_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_5_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_5_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.b cert72_seen_5_25_1 = cert72_layer_5_25_1 := by
  decide

def cert72_seen_5_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_5_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_5_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.b cert72_seen_5_25_2 = cert72_layer_5_25_2 := by
  decide

def cert72_seen_5_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_5_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_5_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.b cert72_seen_5_25_3 = cert72_layer_5_25_3 := by
  decide

def cert72_seen_5_25_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_5_25_4 : List ChainEdge :=
  []

theorem cert72_layer_5_25_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 5 [])
      LColor.r LColor.b cert72_seen_5_25_4 = cert72_layer_5_25_4 := by
  decide

theorem cert72_component_5_25_eq :
    closedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_5_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b 27 cert72_seen_5_25_0 = cert72_component_5_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.b
    cert72_seen_5_25_0 cert72_layer_5_25_0 26 cert72_layer_5_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b 26 cert72_seen_5_25_1 = cert72_component_5_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.b
    cert72_seen_5_25_1 cert72_layer_5_25_1 25 cert72_layer_5_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b 25 cert72_seen_5_25_2 = cert72_component_5_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.b
    cert72_seen_5_25_2 cert72_layer_5_25_2 24 cert72_layer_5_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b 24 cert72_seen_5_25_3 = cert72_component_5_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 5 []) LColor.r LColor.b
    cert72_seen_5_25_3 cert72_layer_5_25_3 23 cert72_layer_5_25_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 5 [])
      LColor.r LColor.b 23 cert72_seen_5_25_4 = cert72_component_5_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 5 []) LColor.r LColor.b
    cert72_seen_5_25_4 cert72_layer_5_25_4_eq 23

theorem cert72_step_5_25 :
    closedCollarIndexStepBool word fiber72 5 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_5_25)
    (by decide) (by decide)
    (by simpa [cert72_move_5_25] using cert72_component_5_25_eq)
    (by decide) (by decide) (by decide)

def cert72_move_6_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_6_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_6_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_6_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.b LColor.p cert72_seen_6_2_0 = cert72_layer_6_2_0 := by
  decide

def cert72_seen_6_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_6_2_1 : List ChainEdge :=
  []

theorem cert72_layer_6_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.b LColor.p cert72_seen_6_2_1 = cert72_layer_6_2_1 := by
  decide

theorem cert72_component_6_2_eq :
    closedCollarComponent word (listGetD fiber72 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_6_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.b LColor.p 27 cert72_seen_6_2_0 = cert72_component_6_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.b LColor.p
    cert72_seen_6_2_0 cert72_layer_6_2_0 26 cert72_layer_6_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.b LColor.p 26 cert72_seen_6_2_1 = cert72_component_6_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 6 []) LColor.b LColor.p
    cert72_seen_6_2_1 cert72_layer_6_2_1_eq 26

theorem cert72_step_6_2 :
    closedCollarIndexStepBool word fiber72 6 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_6_2)
    (by decide) (by decide)
    (by simpa [cert72_move_6_2] using cert72_component_6_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_6_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_6_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_6_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_6_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_6_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.p cert72_seen_6_10_0 = cert72_layer_6_10_0 := by
  decide

def cert72_seen_6_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_6_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_6_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.p cert72_seen_6_10_1 = cert72_layer_6_10_1 := by
  decide

def cert72_seen_6_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_6_10_2 : List ChainEdge :=
  []

theorem cert72_layer_6_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.p cert72_seen_6_10_2 = cert72_layer_6_10_2 := by
  decide

theorem cert72_component_6_10_eq :
    closedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_6_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.p 27 cert72_seen_6_10_0 = cert72_component_6_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.p
    cert72_seen_6_10_0 cert72_layer_6_10_0 26 cert72_layer_6_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.p 26 cert72_seen_6_10_1 = cert72_component_6_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.p
    cert72_seen_6_10_1 cert72_layer_6_10_1 25 cert72_layer_6_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.p 25 cert72_seen_6_10_2 = cert72_component_6_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 6 []) LColor.r LColor.p
    cert72_seen_6_10_2 cert72_layer_6_10_2_eq 25

theorem cert72_step_6_10 :
    closedCollarIndexStepBool word fiber72 6 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_6_10)
    (by decide) (by decide)
    (by simpa [cert72_move_6_10] using cert72_component_6_10_eq)
    (by decide) (by decide) (by decide)

def cert72_move_6_26 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_6_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_6_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_6_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_6_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.b cert72_seen_6_26_0 = cert72_layer_6_26_0 := by
  decide

def cert72_seen_6_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_6_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_6_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.b cert72_seen_6_26_1 = cert72_layer_6_26_1 := by
  decide

def cert72_seen_6_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_6_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_6_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.b cert72_seen_6_26_2 = cert72_layer_6_26_2 := by
  decide

def cert72_seen_6_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_6_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_6_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.b cert72_seen_6_26_3 = cert72_layer_6_26_3 := by
  decide

def cert72_seen_6_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_6_26_4 : List ChainEdge :=
  []

theorem cert72_layer_6_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 6 [])
      LColor.r LColor.b cert72_seen_6_26_4 = cert72_layer_6_26_4 := by
  decide

theorem cert72_component_6_26_eq :
    closedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_6_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b 27 cert72_seen_6_26_0 = cert72_component_6_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.b
    cert72_seen_6_26_0 cert72_layer_6_26_0 26 cert72_layer_6_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b 26 cert72_seen_6_26_1 = cert72_component_6_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.b
    cert72_seen_6_26_1 cert72_layer_6_26_1 25 cert72_layer_6_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b 25 cert72_seen_6_26_2 = cert72_component_6_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.b
    cert72_seen_6_26_2 cert72_layer_6_26_2 24 cert72_layer_6_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b 24 cert72_seen_6_26_3 = cert72_component_6_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 6 []) LColor.r LColor.b
    cert72_seen_6_26_3 cert72_layer_6_26_3 23 cert72_layer_6_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 6 [])
      LColor.r LColor.b 23 cert72_seen_6_26_4 = cert72_component_6_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 6 []) LColor.r LColor.b
    cert72_seen_6_26_4 cert72_layer_6_26_4_eq 23

theorem cert72_step_6_26 :
    closedCollarIndexStepBool word fiber72 6 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_6_26)
    (by decide) (by decide)
    (by simpa [cert72_move_6_26] using cert72_component_6_26_eq)
    (by decide) (by decide) (by decide)

def cert72_move_7_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert72_component_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_seen_7_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert72_layer_7_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert72_layer_7_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.b LColor.p cert72_seen_7_3_0 = cert72_layer_7_3_0 := by
  decide

def cert72_seen_7_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert72_layer_7_3_1 : List ChainEdge :=
  []

theorem cert72_layer_7_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.b LColor.p cert72_seen_7_3_1 = cert72_layer_7_3_1 := by
  decide

theorem cert72_component_7_3_eq :
    closedCollarComponent word (listGetD fiber72 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert72_component_7_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.b LColor.p 27 cert72_seen_7_3_0 = cert72_component_7_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.b LColor.p
    cert72_seen_7_3_0 cert72_layer_7_3_0 26 cert72_layer_7_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.b LColor.p 26 cert72_seen_7_3_1 = cert72_component_7_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 7 []) LColor.b LColor.p
    cert72_seen_7_3_1 cert72_layer_7_3_1_eq 26

theorem cert72_step_7_3 :
    closedCollarIndexStepBool word fiber72 7 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_7_3)
    (by decide) (by decide)
    (by simpa [cert72_move_7_3] using cert72_component_7_3_eq)
    (by decide) (by decide) (by decide)

def cert72_move_7_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_7_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_7_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_7_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_7_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.p cert72_seen_7_11_0 = cert72_layer_7_11_0 := by
  decide

def cert72_seen_7_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_7_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_7_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.p cert72_seen_7_11_1 = cert72_layer_7_11_1 := by
  decide

def cert72_seen_7_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_7_11_2 : List ChainEdge :=
  []

theorem cert72_layer_7_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.p cert72_seen_7_11_2 = cert72_layer_7_11_2 := by
  decide

theorem cert72_component_7_11_eq :
    closedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_7_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.p 27 cert72_seen_7_11_0 = cert72_component_7_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.p
    cert72_seen_7_11_0 cert72_layer_7_11_0 26 cert72_layer_7_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.p 26 cert72_seen_7_11_1 = cert72_component_7_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.p
    cert72_seen_7_11_1 cert72_layer_7_11_1 25 cert72_layer_7_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.p 25 cert72_seen_7_11_2 = cert72_component_7_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 7 []) LColor.r LColor.p
    cert72_seen_7_11_2 cert72_layer_7_11_2_eq 25

theorem cert72_step_7_11 :
    closedCollarIndexStepBool word fiber72 7 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_7_11)
    (by decide) (by decide)
    (by simpa [cert72_move_7_11] using cert72_component_7_11_eq)
    (by decide) (by decide) (by decide)

def cert72_move_7_27 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_7_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_7_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_7_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_7_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.b cert72_seen_7_27_0 = cert72_layer_7_27_0 := by
  decide

def cert72_seen_7_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_7_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_7_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.b cert72_seen_7_27_1 = cert72_layer_7_27_1 := by
  decide

def cert72_seen_7_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_7_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_7_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.b cert72_seen_7_27_2 = cert72_layer_7_27_2 := by
  decide

def cert72_seen_7_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_7_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_7_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.b cert72_seen_7_27_3 = cert72_layer_7_27_3 := by
  decide

def cert72_seen_7_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_7_27_4 : List ChainEdge :=
  []

theorem cert72_layer_7_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 7 [])
      LColor.r LColor.b cert72_seen_7_27_4 = cert72_layer_7_27_4 := by
  decide

theorem cert72_component_7_27_eq :
    closedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_7_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b 27 cert72_seen_7_27_0 = cert72_component_7_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.b
    cert72_seen_7_27_0 cert72_layer_7_27_0 26 cert72_layer_7_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b 26 cert72_seen_7_27_1 = cert72_component_7_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.b
    cert72_seen_7_27_1 cert72_layer_7_27_1 25 cert72_layer_7_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b 25 cert72_seen_7_27_2 = cert72_component_7_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.b
    cert72_seen_7_27_2 cert72_layer_7_27_2 24 cert72_layer_7_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b 24 cert72_seen_7_27_3 = cert72_component_7_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 7 []) LColor.r LColor.b
    cert72_seen_7_27_3 cert72_layer_7_27_3 23 cert72_layer_7_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 7 [])
      LColor.r LColor.b 23 cert72_seen_7_27_4 = cert72_component_7_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 7 []) LColor.r LColor.b
    cert72_seen_7_27_4 cert72_layer_7_27_4_eq 23

theorem cert72_step_7_27 :
    closedCollarIndexStepBool word fiber72 7 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_7_27)
    (by decide) (by decide)
    (by simpa [cert72_move_7_27] using cert72_component_7_27_eq)
    (by decide) (by decide) (by decide)

def cert72_move_8_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_8_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_8_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_8_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_8_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 8 [])
      LColor.r LColor.p cert72_seen_8_4_0 = cert72_layer_8_4_0 := by
  decide

def cert72_seen_8_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_8_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_8_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 8 [])
      LColor.r LColor.p cert72_seen_8_4_1 = cert72_layer_8_4_1 := by
  decide

def cert72_seen_8_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_8_4_2 : List ChainEdge :=
  []

theorem cert72_layer_8_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 8 [])
      LColor.r LColor.p cert72_seen_8_4_2 = cert72_layer_8_4_2 := by
  decide

theorem cert72_component_8_4_eq :
    closedCollarComponent word (listGetD fiber72 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_8_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 8 [])
      LColor.r LColor.p 27 cert72_seen_8_4_0 = cert72_component_8_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 8 []) LColor.r LColor.p
    cert72_seen_8_4_0 cert72_layer_8_4_0 26 cert72_layer_8_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 8 [])
      LColor.r LColor.p 26 cert72_seen_8_4_1 = cert72_component_8_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 8 []) LColor.r LColor.p
    cert72_seen_8_4_1 cert72_layer_8_4_1 25 cert72_layer_8_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 8 [])
      LColor.r LColor.p 25 cert72_seen_8_4_2 = cert72_component_8_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 8 []) LColor.r LColor.p
    cert72_seen_8_4_2 cert72_layer_8_4_2_eq 25

theorem cert72_step_8_4 :
    closedCollarIndexStepBool word fiber72 8 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_8_4)
    (by decide) (by decide)
    (by simpa [cert72_move_8_4] using cert72_component_8_4_eq)
    (by decide) (by decide) (by decide)

def cert72_move_9_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_9_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_9_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_9_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_9_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 9 [])
      LColor.r LColor.p cert72_seen_9_5_0 = cert72_layer_9_5_0 := by
  decide

def cert72_seen_9_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_9_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_9_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 9 [])
      LColor.r LColor.p cert72_seen_9_5_1 = cert72_layer_9_5_1 := by
  decide

def cert72_seen_9_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_9_5_2 : List ChainEdge :=
  []

theorem cert72_layer_9_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 9 [])
      LColor.r LColor.p cert72_seen_9_5_2 = cert72_layer_9_5_2 := by
  decide

theorem cert72_component_9_5_eq :
    closedCollarComponent word (listGetD fiber72 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_9_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 9 [])
      LColor.r LColor.p 27 cert72_seen_9_5_0 = cert72_component_9_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 9 []) LColor.r LColor.p
    cert72_seen_9_5_0 cert72_layer_9_5_0 26 cert72_layer_9_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 9 [])
      LColor.r LColor.p 26 cert72_seen_9_5_1 = cert72_component_9_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 9 []) LColor.r LColor.p
    cert72_seen_9_5_1 cert72_layer_9_5_1 25 cert72_layer_9_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 9 [])
      LColor.r LColor.p 25 cert72_seen_9_5_2 = cert72_component_9_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 9 []) LColor.r LColor.p
    cert72_seen_9_5_2 cert72_layer_9_5_2_eq 25

theorem cert72_step_9_5 :
    closedCollarIndexStepBool word fiber72 9 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_9_5)
    (by decide) (by decide)
    (by simpa [cert72_move_9_5] using cert72_component_9_5_eq)
    (by decide) (by decide) (by decide)

def cert72_move_10_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_10_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_10_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_10_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_10_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 10 [])
      LColor.r LColor.p cert72_seen_10_6_0 = cert72_layer_10_6_0 := by
  decide

def cert72_seen_10_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_10_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_10_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 10 [])
      LColor.r LColor.p cert72_seen_10_6_1 = cert72_layer_10_6_1 := by
  decide

def cert72_seen_10_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_10_6_2 : List ChainEdge :=
  []

theorem cert72_layer_10_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 10 [])
      LColor.r LColor.p cert72_seen_10_6_2 = cert72_layer_10_6_2 := by
  decide

theorem cert72_component_10_6_eq :
    closedCollarComponent word (listGetD fiber72 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_10_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 10 [])
      LColor.r LColor.p 27 cert72_seen_10_6_0 = cert72_component_10_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 10 []) LColor.r LColor.p
    cert72_seen_10_6_0 cert72_layer_10_6_0 26 cert72_layer_10_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 10 [])
      LColor.r LColor.p 26 cert72_seen_10_6_1 = cert72_component_10_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 10 []) LColor.r LColor.p
    cert72_seen_10_6_1 cert72_layer_10_6_1 25 cert72_layer_10_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 10 [])
      LColor.r LColor.p 25 cert72_seen_10_6_2 = cert72_component_10_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 10 []) LColor.r LColor.p
    cert72_seen_10_6_2 cert72_layer_10_6_2_eq 25

theorem cert72_step_10_6 :
    closedCollarIndexStepBool word fiber72 10 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_10_6)
    (by decide) (by decide)
    (by simpa [cert72_move_10_6] using cert72_component_10_6_eq)
    (by decide) (by decide) (by decide)

def cert72_move_11_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_11_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_11_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_11_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_11_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 11 [])
      LColor.r LColor.p cert72_seen_11_7_0 = cert72_layer_11_7_0 := by
  decide

def cert72_seen_11_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_11_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_11_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 11 [])
      LColor.r LColor.p cert72_seen_11_7_1 = cert72_layer_11_7_1 := by
  decide

def cert72_seen_11_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_11_7_2 : List ChainEdge :=
  []

theorem cert72_layer_11_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 11 [])
      LColor.r LColor.p cert72_seen_11_7_2 = cert72_layer_11_7_2 := by
  decide

theorem cert72_component_11_7_eq :
    closedCollarComponent word (listGetD fiber72 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_11_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 11 [])
      LColor.r LColor.p 27 cert72_seen_11_7_0 = cert72_component_11_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 11 []) LColor.r LColor.p
    cert72_seen_11_7_0 cert72_layer_11_7_0 26 cert72_layer_11_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 11 [])
      LColor.r LColor.p 26 cert72_seen_11_7_1 = cert72_component_11_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 11 []) LColor.r LColor.p
    cert72_seen_11_7_1 cert72_layer_11_7_1 25 cert72_layer_11_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 11 [])
      LColor.r LColor.p 25 cert72_seen_11_7_2 = cert72_component_11_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 11 []) LColor.r LColor.p
    cert72_seen_11_7_2 cert72_layer_11_7_2_eq 25

theorem cert72_step_11_7 :
    closedCollarIndexStepBool word fiber72 11 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_11_7)
    (by decide) (by decide)
    (by simpa [cert72_move_11_7] using cert72_component_11_7_eq)
    (by decide) (by decide) (by decide)

def cert72_move_12_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_12_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.p cert72_seen_12_0_0 = cert72_layer_12_0_0 := by
  decide

def cert72_seen_12_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_12_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_12_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.p cert72_seen_12_0_1 = cert72_layer_12_0_1 := by
  decide

def cert72_seen_12_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_12_0_2 : List ChainEdge :=
  []

theorem cert72_layer_12_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.p cert72_seen_12_0_2 = cert72_layer_12_0_2 := by
  decide

theorem cert72_component_12_0_eq :
    closedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_12_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.p 27 cert72_seen_12_0_0 = cert72_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 12 []) LColor.r LColor.p
    cert72_seen_12_0_0 cert72_layer_12_0_0 26 cert72_layer_12_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.p 26 cert72_seen_12_0_1 = cert72_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 12 []) LColor.r LColor.p
    cert72_seen_12_0_1 cert72_layer_12_0_1 25 cert72_layer_12_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.p 25 cert72_seen_12_0_2 = cert72_component_12_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 12 []) LColor.r LColor.p
    cert72_seen_12_0_2 cert72_layer_12_0_2_eq 25

theorem cert72_step_12_0 :
    closedCollarIndexStepBool word fiber72 12 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_12_0)
    (by decide) (by decide)
    (by simpa [cert72_move_12_0] using cert72_component_12_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_12_40 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_12_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_12_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_12_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_12_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.b cert72_seen_12_40_0 = cert72_layer_12_40_0 := by
  decide

def cert72_seen_12_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_12_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_12_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.b cert72_seen_12_40_1 = cert72_layer_12_40_1 := by
  decide

def cert72_seen_12_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_12_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_12_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.b cert72_seen_12_40_2 = cert72_layer_12_40_2 := by
  decide

def cert72_seen_12_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_12_40_3 : List ChainEdge :=
  []

theorem cert72_layer_12_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 12 [])
      LColor.r LColor.b cert72_seen_12_40_3 = cert72_layer_12_40_3 := by
  decide

theorem cert72_component_12_40_eq :
    closedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_12_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.b 27 cert72_seen_12_40_0 = cert72_component_12_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 12 []) LColor.r LColor.b
    cert72_seen_12_40_0 cert72_layer_12_40_0 26 cert72_layer_12_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.b 26 cert72_seen_12_40_1 = cert72_component_12_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 12 []) LColor.r LColor.b
    cert72_seen_12_40_1 cert72_layer_12_40_1 25 cert72_layer_12_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.b 25 cert72_seen_12_40_2 = cert72_component_12_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 12 []) LColor.r LColor.b
    cert72_seen_12_40_2 cert72_layer_12_40_2 24 cert72_layer_12_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 12 [])
      LColor.r LColor.b 24 cert72_seen_12_40_3 = cert72_component_12_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 12 []) LColor.r LColor.b
    cert72_seen_12_40_3 cert72_layer_12_40_3_eq 24

theorem cert72_step_12_40 :
    closedCollarIndexStepBool word fiber72 12 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_12_40)
    (by decide) (by decide)
    (by simpa [cert72_move_12_40] using cert72_component_12_40_eq)
    (by decide) (by decide) (by decide)

def cert72_move_13_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_13_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.p cert72_seen_13_1_0 = cert72_layer_13_1_0 := by
  decide

def cert72_seen_13_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_13_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_13_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.p cert72_seen_13_1_1 = cert72_layer_13_1_1 := by
  decide

def cert72_seen_13_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_13_1_2 : List ChainEdge :=
  []

theorem cert72_layer_13_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.p cert72_seen_13_1_2 = cert72_layer_13_1_2 := by
  decide

theorem cert72_component_13_1_eq :
    closedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_13_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.p 27 cert72_seen_13_1_0 = cert72_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 13 []) LColor.r LColor.p
    cert72_seen_13_1_0 cert72_layer_13_1_0 26 cert72_layer_13_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.p 26 cert72_seen_13_1_1 = cert72_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 13 []) LColor.r LColor.p
    cert72_seen_13_1_1 cert72_layer_13_1_1 25 cert72_layer_13_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.p 25 cert72_seen_13_1_2 = cert72_component_13_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 13 []) LColor.r LColor.p
    cert72_seen_13_1_2 cert72_layer_13_1_2_eq 25

theorem cert72_step_13_1 :
    closedCollarIndexStepBool word fiber72 13 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_13_1)
    (by decide) (by decide)
    (by simpa [cert72_move_13_1] using cert72_component_13_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_13_41 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_13_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_13_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_13_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_13_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.b cert72_seen_13_41_0 = cert72_layer_13_41_0 := by
  decide

def cert72_seen_13_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_13_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_13_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.b cert72_seen_13_41_1 = cert72_layer_13_41_1 := by
  decide

def cert72_seen_13_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_13_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_13_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.b cert72_seen_13_41_2 = cert72_layer_13_41_2 := by
  decide

def cert72_seen_13_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_13_41_3 : List ChainEdge :=
  []

theorem cert72_layer_13_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 13 [])
      LColor.r LColor.b cert72_seen_13_41_3 = cert72_layer_13_41_3 := by
  decide

theorem cert72_component_13_41_eq :
    closedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_13_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.b 27 cert72_seen_13_41_0 = cert72_component_13_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 13 []) LColor.r LColor.b
    cert72_seen_13_41_0 cert72_layer_13_41_0 26 cert72_layer_13_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.b 26 cert72_seen_13_41_1 = cert72_component_13_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 13 []) LColor.r LColor.b
    cert72_seen_13_41_1 cert72_layer_13_41_1 25 cert72_layer_13_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.b 25 cert72_seen_13_41_2 = cert72_component_13_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 13 []) LColor.r LColor.b
    cert72_seen_13_41_2 cert72_layer_13_41_2 24 cert72_layer_13_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 13 [])
      LColor.r LColor.b 24 cert72_seen_13_41_3 = cert72_component_13_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 13 []) LColor.r LColor.b
    cert72_seen_13_41_3 cert72_layer_13_41_3_eq 24

theorem cert72_step_13_41 :
    closedCollarIndexStepBool word fiber72 13 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_13_41)
    (by decide) (by decide)
    (by simpa [cert72_move_13_41] using cert72_component_13_41_eq)
    (by decide) (by decide) (by decide)

def cert72_move_14_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_14_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.p cert72_seen_14_2_0 = cert72_layer_14_2_0 := by
  decide

def cert72_seen_14_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_14_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_14_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.p cert72_seen_14_2_1 = cert72_layer_14_2_1 := by
  decide

def cert72_seen_14_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_14_2_2 : List ChainEdge :=
  []

theorem cert72_layer_14_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.p cert72_seen_14_2_2 = cert72_layer_14_2_2 := by
  decide

theorem cert72_component_14_2_eq :
    closedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_14_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.p 27 cert72_seen_14_2_0 = cert72_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 14 []) LColor.r LColor.p
    cert72_seen_14_2_0 cert72_layer_14_2_0 26 cert72_layer_14_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.p 26 cert72_seen_14_2_1 = cert72_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 14 []) LColor.r LColor.p
    cert72_seen_14_2_1 cert72_layer_14_2_1 25 cert72_layer_14_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.p 25 cert72_seen_14_2_2 = cert72_component_14_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 14 []) LColor.r LColor.p
    cert72_seen_14_2_2 cert72_layer_14_2_2_eq 25

theorem cert72_step_14_2 :
    closedCollarIndexStepBool word fiber72 14 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_14_2)
    (by decide) (by decide)
    (by simpa [cert72_move_14_2] using cert72_component_14_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_14_42 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_14_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_14_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_14_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_14_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.b cert72_seen_14_42_0 = cert72_layer_14_42_0 := by
  decide

def cert72_seen_14_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_14_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_14_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.b cert72_seen_14_42_1 = cert72_layer_14_42_1 := by
  decide

def cert72_seen_14_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_14_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_14_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.b cert72_seen_14_42_2 = cert72_layer_14_42_2 := by
  decide

def cert72_seen_14_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_14_42_3 : List ChainEdge :=
  []

theorem cert72_layer_14_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 14 [])
      LColor.r LColor.b cert72_seen_14_42_3 = cert72_layer_14_42_3 := by
  decide

theorem cert72_component_14_42_eq :
    closedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_14_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.b 27 cert72_seen_14_42_0 = cert72_component_14_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 14 []) LColor.r LColor.b
    cert72_seen_14_42_0 cert72_layer_14_42_0 26 cert72_layer_14_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.b 26 cert72_seen_14_42_1 = cert72_component_14_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 14 []) LColor.r LColor.b
    cert72_seen_14_42_1 cert72_layer_14_42_1 25 cert72_layer_14_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.b 25 cert72_seen_14_42_2 = cert72_component_14_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 14 []) LColor.r LColor.b
    cert72_seen_14_42_2 cert72_layer_14_42_2 24 cert72_layer_14_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 14 [])
      LColor.r LColor.b 24 cert72_seen_14_42_3 = cert72_component_14_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 14 []) LColor.r LColor.b
    cert72_seen_14_42_3 cert72_layer_14_42_3_eq 24

theorem cert72_step_14_42 :
    closedCollarIndexStepBool word fiber72 14 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_14_42)
    (by decide) (by decide)
    (by simpa [cert72_move_14_42] using cert72_component_14_42_eq)
    (by decide) (by decide) (by decide)

def cert72_move_15_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_15_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.p cert72_seen_15_3_0 = cert72_layer_15_3_0 := by
  decide

def cert72_seen_15_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_15_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_15_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.p cert72_seen_15_3_1 = cert72_layer_15_3_1 := by
  decide

def cert72_seen_15_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_15_3_2 : List ChainEdge :=
  []

theorem cert72_layer_15_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.p cert72_seen_15_3_2 = cert72_layer_15_3_2 := by
  decide

theorem cert72_component_15_3_eq :
    closedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_15_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.p 27 cert72_seen_15_3_0 = cert72_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 15 []) LColor.r LColor.p
    cert72_seen_15_3_0 cert72_layer_15_3_0 26 cert72_layer_15_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.p 26 cert72_seen_15_3_1 = cert72_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 15 []) LColor.r LColor.p
    cert72_seen_15_3_1 cert72_layer_15_3_1 25 cert72_layer_15_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.p 25 cert72_seen_15_3_2 = cert72_component_15_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 15 []) LColor.r LColor.p
    cert72_seen_15_3_2 cert72_layer_15_3_2_eq 25

theorem cert72_step_15_3 :
    closedCollarIndexStepBool word fiber72 15 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_15_3)
    (by decide) (by decide)
    (by simpa [cert72_move_15_3] using cert72_component_15_3_eq)
    (by decide) (by decide) (by decide)

def cert72_move_15_43 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_15_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_15_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_15_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_15_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.b cert72_seen_15_43_0 = cert72_layer_15_43_0 := by
  decide

def cert72_seen_15_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_15_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_15_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.b cert72_seen_15_43_1 = cert72_layer_15_43_1 := by
  decide

def cert72_seen_15_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_15_43_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_15_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.b cert72_seen_15_43_2 = cert72_layer_15_43_2 := by
  decide

def cert72_seen_15_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_15_43_3 : List ChainEdge :=
  []

theorem cert72_layer_15_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 15 [])
      LColor.r LColor.b cert72_seen_15_43_3 = cert72_layer_15_43_3 := by
  decide

theorem cert72_component_15_43_eq :
    closedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_15_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.b 27 cert72_seen_15_43_0 = cert72_component_15_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 15 []) LColor.r LColor.b
    cert72_seen_15_43_0 cert72_layer_15_43_0 26 cert72_layer_15_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.b 26 cert72_seen_15_43_1 = cert72_component_15_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 15 []) LColor.r LColor.b
    cert72_seen_15_43_1 cert72_layer_15_43_1 25 cert72_layer_15_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.b 25 cert72_seen_15_43_2 = cert72_component_15_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 15 []) LColor.r LColor.b
    cert72_seen_15_43_2 cert72_layer_15_43_2 24 cert72_layer_15_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 15 [])
      LColor.r LColor.b 24 cert72_seen_15_43_3 = cert72_component_15_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 15 []) LColor.r LColor.b
    cert72_seen_15_43_3 cert72_layer_15_43_3_eq 24

theorem cert72_step_15_43 :
    closedCollarIndexStepBool word fiber72 15 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_15_43)
    (by decide) (by decide)
    (by simpa [cert72_move_15_43] using cert72_component_15_43_eq)
    (by decide) (by decide) (by decide)

def cert72_move_16_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_16_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_16_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.r LColor.b cert72_seen_16_0_0 = cert72_layer_16_0_0 := by
  decide

def cert72_seen_16_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_16_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_16_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.r LColor.b cert72_seen_16_0_1 = cert72_layer_16_0_1 := by
  decide

def cert72_seen_16_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_16_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_16_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.r LColor.b cert72_seen_16_0_2 = cert72_layer_16_0_2 := by
  decide

def cert72_seen_16_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_16_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_16_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.r LColor.b cert72_seen_16_0_3 = cert72_layer_16_0_3 := by
  decide

def cert72_seen_16_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_16_0_4 : List ChainEdge :=
  []

theorem cert72_layer_16_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.r LColor.b cert72_seen_16_0_4 = cert72_layer_16_0_4 := by
  decide

theorem cert72_component_16_0_eq :
    closedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_16_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b 27 cert72_seen_16_0_0 = cert72_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.r LColor.b
    cert72_seen_16_0_0 cert72_layer_16_0_0 26 cert72_layer_16_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b 26 cert72_seen_16_0_1 = cert72_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.r LColor.b
    cert72_seen_16_0_1 cert72_layer_16_0_1 25 cert72_layer_16_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b 25 cert72_seen_16_0_2 = cert72_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.r LColor.b
    cert72_seen_16_0_2 cert72_layer_16_0_2 24 cert72_layer_16_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b 24 cert72_seen_16_0_3 = cert72_component_16_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.r LColor.b
    cert72_seen_16_0_3 cert72_layer_16_0_3 23 cert72_layer_16_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.r LColor.b 23 cert72_seen_16_0_4 = cert72_component_16_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 16 []) LColor.r LColor.b
    cert72_seen_16_0_4 cert72_layer_16_0_4_eq 23

theorem cert72_step_16_0 :
    closedCollarIndexStepBool word fiber72 16 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_16_0)
    (by decide) (by decide)
    (by simpa [cert72_move_16_0] using cert72_component_16_0_eq)
    (by decide) (by decide) (by decide)

def cert72_move_16_20 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_16_20 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_16_20_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_16_20_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_16_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_20_0 = cert72_layer_16_20_0 := by
  decide

def cert72_seen_16_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_16_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_16_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_20_1 = cert72_layer_16_20_1 := by
  decide

def cert72_seen_16_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_16_20_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_16_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_20_2 = cert72_layer_16_20_2 := by
  decide

def cert72_seen_16_20_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_16_20_3 : List ChainEdge :=
  []

theorem cert72_layer_16_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_20_3 = cert72_layer_16_20_3 := by
  decide

theorem cert72_component_16_20_eq :
    closedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_16_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 16 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 27 cert72_seen_16_20_0 = cert72_component_16_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_20_0 cert72_layer_16_20_0 26 cert72_layer_16_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 26 cert72_seen_16_20_1 = cert72_component_16_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_20_1 cert72_layer_16_20_1 25 cert72_layer_16_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 25 cert72_seen_16_20_2 = cert72_component_16_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_20_2 cert72_layer_16_20_2 24 cert72_layer_16_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 24 cert72_seen_16_20_3 = cert72_component_16_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_20_3 cert72_layer_16_20_3_eq 24

theorem cert72_step_16_20 :
    closedCollarIndexStepBool word fiber72 16 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_16_20)
    (by decide) (by decide)
    (by simpa [cert72_move_16_20] using cert72_component_16_20_eq)
    (by decide) (by decide) (by decide)

def cert72_move_16_32 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_16_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_16_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_16_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_16_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_32_0 = cert72_layer_16_32_0 := by
  decide

def cert72_seen_16_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_16_32_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_16_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_32_1 = cert72_layer_16_32_1 := by
  decide

def cert72_seen_16_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_16_32_2 : List ChainEdge :=
  []

theorem cert72_layer_16_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 16 [])
      LColor.b LColor.p cert72_seen_16_32_2 = cert72_layer_16_32_2 := by
  decide

theorem cert72_component_16_32_eq :
    closedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_16_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 16 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 27 cert72_seen_16_32_0 = cert72_component_16_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_32_0 cert72_layer_16_32_0 26 cert72_layer_16_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 26 cert72_seen_16_32_1 = cert72_component_16_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_32_1 cert72_layer_16_32_1 25 cert72_layer_16_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 16 [])
      LColor.b LColor.p 25 cert72_seen_16_32_2 = cert72_component_16_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 16 []) LColor.b LColor.p
    cert72_seen_16_32_2 cert72_layer_16_32_2_eq 25

theorem cert72_step_16_32 :
    closedCollarIndexStepBool word fiber72 16 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_16_32)
    (by decide) (by decide)
    (by simpa [cert72_move_16_32] using cert72_component_16_32_eq)
    (by decide) (by decide) (by decide)

def cert72_move_17_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_17_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_17_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.r LColor.b cert72_seen_17_1_0 = cert72_layer_17_1_0 := by
  decide

def cert72_seen_17_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_17_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_17_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.r LColor.b cert72_seen_17_1_1 = cert72_layer_17_1_1 := by
  decide

def cert72_seen_17_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_17_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_17_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.r LColor.b cert72_seen_17_1_2 = cert72_layer_17_1_2 := by
  decide

def cert72_seen_17_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_17_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_17_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.r LColor.b cert72_seen_17_1_3 = cert72_layer_17_1_3 := by
  decide

def cert72_seen_17_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_17_1_4 : List ChainEdge :=
  []

theorem cert72_layer_17_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.r LColor.b cert72_seen_17_1_4 = cert72_layer_17_1_4 := by
  decide

theorem cert72_component_17_1_eq :
    closedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_17_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b 27 cert72_seen_17_1_0 = cert72_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.r LColor.b
    cert72_seen_17_1_0 cert72_layer_17_1_0 26 cert72_layer_17_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b 26 cert72_seen_17_1_1 = cert72_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.r LColor.b
    cert72_seen_17_1_1 cert72_layer_17_1_1 25 cert72_layer_17_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b 25 cert72_seen_17_1_2 = cert72_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.r LColor.b
    cert72_seen_17_1_2 cert72_layer_17_1_2 24 cert72_layer_17_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b 24 cert72_seen_17_1_3 = cert72_component_17_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.r LColor.b
    cert72_seen_17_1_3 cert72_layer_17_1_3 23 cert72_layer_17_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.r LColor.b 23 cert72_seen_17_1_4 = cert72_component_17_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 17 []) LColor.r LColor.b
    cert72_seen_17_1_4 cert72_layer_17_1_4_eq 23

theorem cert72_step_17_1 :
    closedCollarIndexStepBool word fiber72 17 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_17_1)
    (by decide) (by decide)
    (by simpa [cert72_move_17_1] using cert72_component_17_1_eq)
    (by decide) (by decide) (by decide)

def cert72_move_17_21 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_17_21 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_17_21_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_17_21_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_17_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_21_0 = cert72_layer_17_21_0 := by
  decide

def cert72_seen_17_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_17_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_17_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_21_1 = cert72_layer_17_21_1 := by
  decide

def cert72_seen_17_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_17_21_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_17_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_21_2 = cert72_layer_17_21_2 := by
  decide

def cert72_seen_17_21_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_17_21_3 : List ChainEdge :=
  []

theorem cert72_layer_17_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_21_3 = cert72_layer_17_21_3 := by
  decide

theorem cert72_component_17_21_eq :
    closedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_17_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 17 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 27 cert72_seen_17_21_0 = cert72_component_17_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_21_0 cert72_layer_17_21_0 26 cert72_layer_17_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 26 cert72_seen_17_21_1 = cert72_component_17_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_21_1 cert72_layer_17_21_1 25 cert72_layer_17_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 25 cert72_seen_17_21_2 = cert72_component_17_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_21_2 cert72_layer_17_21_2 24 cert72_layer_17_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 24 cert72_seen_17_21_3 = cert72_component_17_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_21_3 cert72_layer_17_21_3_eq 24

theorem cert72_step_17_21 :
    closedCollarIndexStepBool word fiber72 17 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_17_21)
    (by decide) (by decide)
    (by simpa [cert72_move_17_21] using cert72_component_17_21_eq)
    (by decide) (by decide) (by decide)

def cert72_move_17_33 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_17_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_17_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_17_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_17_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_33_0 = cert72_layer_17_33_0 := by
  decide

def cert72_seen_17_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_17_33_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_17_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_33_1 = cert72_layer_17_33_1 := by
  decide

def cert72_seen_17_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_17_33_2 : List ChainEdge :=
  []

theorem cert72_layer_17_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 17 [])
      LColor.b LColor.p cert72_seen_17_33_2 = cert72_layer_17_33_2 := by
  decide

theorem cert72_component_17_33_eq :
    closedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_17_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 17 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 27 cert72_seen_17_33_0 = cert72_component_17_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_33_0 cert72_layer_17_33_0 26 cert72_layer_17_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 26 cert72_seen_17_33_1 = cert72_component_17_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_33_1 cert72_layer_17_33_1 25 cert72_layer_17_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 17 [])
      LColor.b LColor.p 25 cert72_seen_17_33_2 = cert72_component_17_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 17 []) LColor.b LColor.p
    cert72_seen_17_33_2 cert72_layer_17_33_2_eq 25

theorem cert72_step_17_33 :
    closedCollarIndexStepBool word fiber72 17 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_17_33)
    (by decide) (by decide)
    (by simpa [cert72_move_17_33] using cert72_component_17_33_eq)
    (by decide) (by decide) (by decide)

def cert72_move_18_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_18_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_18_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.r LColor.b cert72_seen_18_2_0 = cert72_layer_18_2_0 := by
  decide

def cert72_seen_18_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_18_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_18_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.r LColor.b cert72_seen_18_2_1 = cert72_layer_18_2_1 := by
  decide

def cert72_seen_18_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_18_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_18_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.r LColor.b cert72_seen_18_2_2 = cert72_layer_18_2_2 := by
  decide

def cert72_seen_18_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_18_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_18_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.r LColor.b cert72_seen_18_2_3 = cert72_layer_18_2_3 := by
  decide

def cert72_seen_18_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_18_2_4 : List ChainEdge :=
  []

theorem cert72_layer_18_2_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.r LColor.b cert72_seen_18_2_4 = cert72_layer_18_2_4 := by
  decide

theorem cert72_component_18_2_eq :
    closedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_18_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b 27 cert72_seen_18_2_0 = cert72_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.r LColor.b
    cert72_seen_18_2_0 cert72_layer_18_2_0 26 cert72_layer_18_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b 26 cert72_seen_18_2_1 = cert72_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.r LColor.b
    cert72_seen_18_2_1 cert72_layer_18_2_1 25 cert72_layer_18_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b 25 cert72_seen_18_2_2 = cert72_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.r LColor.b
    cert72_seen_18_2_2 cert72_layer_18_2_2 24 cert72_layer_18_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b 24 cert72_seen_18_2_3 = cert72_component_18_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.r LColor.b
    cert72_seen_18_2_3 cert72_layer_18_2_3 23 cert72_layer_18_2_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.r LColor.b 23 cert72_seen_18_2_4 = cert72_component_18_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 18 []) LColor.r LColor.b
    cert72_seen_18_2_4 cert72_layer_18_2_4_eq 23

theorem cert72_step_18_2 :
    closedCollarIndexStepBool word fiber72 18 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_18_2)
    (by decide) (by decide)
    (by simpa [cert72_move_18_2] using cert72_component_18_2_eq)
    (by decide) (by decide) (by decide)

def cert72_move_18_22 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_18_22 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_18_22_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_18_22_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_18_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_22_0 = cert72_layer_18_22_0 := by
  decide

def cert72_seen_18_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_18_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_18_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_22_1 = cert72_layer_18_22_1 := by
  decide

def cert72_seen_18_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_18_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_18_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_22_2 = cert72_layer_18_22_2 := by
  decide

def cert72_seen_18_22_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_18_22_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_18_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_22_3 = cert72_layer_18_22_3 := by
  decide

def cert72_seen_18_22_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_18_22_4 : List ChainEdge :=
  []

theorem cert72_layer_18_22_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_22_4 = cert72_layer_18_22_4 := by
  decide

theorem cert72_component_18_22_eq :
    closedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_18_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 18 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 27 cert72_seen_18_22_0 = cert72_component_18_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_22_0 cert72_layer_18_22_0 26 cert72_layer_18_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 26 cert72_seen_18_22_1 = cert72_component_18_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_22_1 cert72_layer_18_22_1 25 cert72_layer_18_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 25 cert72_seen_18_22_2 = cert72_component_18_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_22_2 cert72_layer_18_22_2 24 cert72_layer_18_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 24 cert72_seen_18_22_3 = cert72_component_18_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_22_3 cert72_layer_18_22_3 23 cert72_layer_18_22_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 23 cert72_seen_18_22_4 = cert72_component_18_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_22_4 cert72_layer_18_22_4_eq 23

theorem cert72_step_18_22 :
    closedCollarIndexStepBool word fiber72 18 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_18_22)
    (by decide) (by decide)
    (by simpa [cert72_move_18_22] using cert72_component_18_22_eq)
    (by decide) (by decide) (by decide)

def cert72_move_18_34 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_18_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_18_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_18_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_18_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_34_0 = cert72_layer_18_34_0 := by
  decide

def cert72_seen_18_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_18_34_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_18_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_34_1 = cert72_layer_18_34_1 := by
  decide

def cert72_seen_18_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_18_34_2 : List ChainEdge :=
  []

theorem cert72_layer_18_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 18 [])
      LColor.b LColor.p cert72_seen_18_34_2 = cert72_layer_18_34_2 := by
  decide

theorem cert72_component_18_34_eq :
    closedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_18_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 18 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 27 cert72_seen_18_34_0 = cert72_component_18_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_34_0 cert72_layer_18_34_0 26 cert72_layer_18_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 26 cert72_seen_18_34_1 = cert72_component_18_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_34_1 cert72_layer_18_34_1 25 cert72_layer_18_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 18 [])
      LColor.b LColor.p 25 cert72_seen_18_34_2 = cert72_component_18_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 18 []) LColor.b LColor.p
    cert72_seen_18_34_2 cert72_layer_18_34_2_eq 25

theorem cert72_step_18_34 :
    closedCollarIndexStepBool word fiber72 18 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_18_34)
    (by decide) (by decide)
    (by simpa [cert72_move_18_34] using cert72_component_18_34_eq)
    (by decide) (by decide) (by decide)

def cert72_move_19_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_19_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_19_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.r LColor.b cert72_seen_19_3_0 = cert72_layer_19_3_0 := by
  decide

def cert72_seen_19_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_19_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_19_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.r LColor.b cert72_seen_19_3_1 = cert72_layer_19_3_1 := by
  decide

def cert72_seen_19_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_19_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_19_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.r LColor.b cert72_seen_19_3_2 = cert72_layer_19_3_2 := by
  decide

def cert72_seen_19_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_19_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_19_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.r LColor.b cert72_seen_19_3_3 = cert72_layer_19_3_3 := by
  decide

def cert72_seen_19_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_19_3_4 : List ChainEdge :=
  []

theorem cert72_layer_19_3_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.r LColor.b cert72_seen_19_3_4 = cert72_layer_19_3_4 := by
  decide

theorem cert72_component_19_3_eq :
    closedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_19_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b 27 cert72_seen_19_3_0 = cert72_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.r LColor.b
    cert72_seen_19_3_0 cert72_layer_19_3_0 26 cert72_layer_19_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b 26 cert72_seen_19_3_1 = cert72_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.r LColor.b
    cert72_seen_19_3_1 cert72_layer_19_3_1 25 cert72_layer_19_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b 25 cert72_seen_19_3_2 = cert72_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.r LColor.b
    cert72_seen_19_3_2 cert72_layer_19_3_2 24 cert72_layer_19_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b 24 cert72_seen_19_3_3 = cert72_component_19_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.r LColor.b
    cert72_seen_19_3_3 cert72_layer_19_3_3 23 cert72_layer_19_3_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.r LColor.b 23 cert72_seen_19_3_4 = cert72_component_19_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 19 []) LColor.r LColor.b
    cert72_seen_19_3_4 cert72_layer_19_3_4_eq 23

theorem cert72_step_19_3 :
    closedCollarIndexStepBool word fiber72 19 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_19_3)
    (by decide) (by decide)
    (by simpa [cert72_move_19_3] using cert72_component_19_3_eq)
    (by decide) (by decide) (by decide)

def cert72_move_19_35 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_19_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_19_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_19_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_19_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.b LColor.p cert72_seen_19_35_0 = cert72_layer_19_35_0 := by
  decide

def cert72_seen_19_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_19_35_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_19_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.b LColor.p cert72_seen_19_35_1 = cert72_layer_19_35_1 := by
  decide

def cert72_seen_19_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_19_35_2 : List ChainEdge :=
  []

theorem cert72_layer_19_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 19 [])
      LColor.b LColor.p cert72_seen_19_35_2 = cert72_layer_19_35_2 := by
  decide

theorem cert72_component_19_35_eq :
    closedCollarComponent word (listGetD fiber72 19 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_19_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 19 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.b LColor.p 27 cert72_seen_19_35_0 = cert72_component_19_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.b LColor.p
    cert72_seen_19_35_0 cert72_layer_19_35_0 26 cert72_layer_19_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.b LColor.p 26 cert72_seen_19_35_1 = cert72_component_19_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 19 []) LColor.b LColor.p
    cert72_seen_19_35_1 cert72_layer_19_35_1 25 cert72_layer_19_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 19 [])
      LColor.b LColor.p 25 cert72_seen_19_35_2 = cert72_component_19_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 19 []) LColor.b LColor.p
    cert72_seen_19_35_2 cert72_layer_19_35_2_eq 25

theorem cert72_step_19_35 :
    closedCollarIndexStepBool word fiber72 19 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_19_35)
    (by decide) (by decide)
    (by simpa [cert72_move_19_35] using cert72_component_19_35_eq)
    (by decide) (by decide) (by decide)

def cert72_move_20_16 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_20_16 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_20_16_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_20_16_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_20_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_16_0 = cert72_layer_20_16_0 := by
  decide

def cert72_seen_20_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_20_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_20_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_16_1 = cert72_layer_20_16_1 := by
  decide

def cert72_seen_20_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_20_16_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_20_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_16_2 = cert72_layer_20_16_2 := by
  decide

def cert72_seen_20_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_20_16_3 : List ChainEdge :=
  []

theorem cert72_layer_20_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_16_3 = cert72_layer_20_16_3 := by
  decide

theorem cert72_component_20_16_eq :
    closedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_20_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 20 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 27 cert72_seen_20_16_0 = cert72_component_20_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_16_0 cert72_layer_20_16_0 26 cert72_layer_20_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 26 cert72_seen_20_16_1 = cert72_component_20_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_16_1 cert72_layer_20_16_1 25 cert72_layer_20_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 25 cert72_seen_20_16_2 = cert72_component_20_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_16_2 cert72_layer_20_16_2 24 cert72_layer_20_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 24 cert72_seen_20_16_3 = cert72_component_20_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_16_3 cert72_layer_20_16_3_eq 24

theorem cert72_step_20_16 :
    closedCollarIndexStepBool word fiber72 20 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_20_16)
    (by decide) (by decide)
    (by simpa [cert72_move_20_16] using cert72_component_20_16_eq)
    (by decide) (by decide) (by decide)

def cert72_move_20_23 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_20_23 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_20_23_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_20_23_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_20_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.r LColor.p cert72_seen_20_23_0 = cert72_layer_20_23_0 := by
  decide

def cert72_seen_20_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_20_23_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_20_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.r LColor.p cert72_seen_20_23_1 = cert72_layer_20_23_1 := by
  decide

def cert72_seen_20_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_20_23_2 : List ChainEdge :=
  []

theorem cert72_layer_20_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.r LColor.p cert72_seen_20_23_2 = cert72_layer_20_23_2 := by
  decide

theorem cert72_component_20_23_eq :
    closedCollarComponent word (listGetD fiber72 20 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_20_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 20 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.r LColor.p 27 cert72_seen_20_23_0 = cert72_component_20_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.r LColor.p
    cert72_seen_20_23_0 cert72_layer_20_23_0 26 cert72_layer_20_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.r LColor.p 26 cert72_seen_20_23_1 = cert72_component_20_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.r LColor.p
    cert72_seen_20_23_1 cert72_layer_20_23_1 25 cert72_layer_20_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.r LColor.p 25 cert72_seen_20_23_2 = cert72_component_20_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 20 []) LColor.r LColor.p
    cert72_seen_20_23_2 cert72_layer_20_23_2_eq 25

theorem cert72_step_20_23 :
    closedCollarIndexStepBool word fiber72 20 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_20_23)
    (by decide) (by decide)
    (by simpa [cert72_move_20_23] using cert72_component_20_23_eq)
    (by decide) (by decide) (by decide)

def cert72_move_20_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_20_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_20_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_20_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_20_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_36_0 = cert72_layer_20_36_0 := by
  decide

def cert72_seen_20_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_20_36_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_20_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_36_1 = cert72_layer_20_36_1 := by
  decide

def cert72_seen_20_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_20_36_2 : List ChainEdge :=
  []

theorem cert72_layer_20_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 20 [])
      LColor.b LColor.p cert72_seen_20_36_2 = cert72_layer_20_36_2 := by
  decide

theorem cert72_component_20_36_eq :
    closedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_20_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 27 cert72_seen_20_36_0 = cert72_component_20_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_36_0 cert72_layer_20_36_0 26 cert72_layer_20_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 26 cert72_seen_20_36_1 = cert72_component_20_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_36_1 cert72_layer_20_36_1 25 cert72_layer_20_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 20 [])
      LColor.b LColor.p 25 cert72_seen_20_36_2 = cert72_component_20_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 20 []) LColor.b LColor.p
    cert72_seen_20_36_2 cert72_layer_20_36_2_eq 25

theorem cert72_step_20_36 :
    closedCollarIndexStepBool word fiber72 20 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_20_36)
    (by decide) (by decide)
    (by simpa [cert72_move_20_36] using cert72_component_20_36_eq)
    (by decide) (by decide) (by decide)

def cert72_move_21_17 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_21_17 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_21_17_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_21_17_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_21_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_17_0 = cert72_layer_21_17_0 := by
  decide

def cert72_seen_21_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_21_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_21_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_17_1 = cert72_layer_21_17_1 := by
  decide

def cert72_seen_21_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_21_17_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_21_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_17_2 = cert72_layer_21_17_2 := by
  decide

def cert72_seen_21_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_21_17_3 : List ChainEdge :=
  []

theorem cert72_layer_21_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_17_3 = cert72_layer_21_17_3 := by
  decide

theorem cert72_component_21_17_eq :
    closedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_21_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 21 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 27 cert72_seen_21_17_0 = cert72_component_21_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_17_0 cert72_layer_21_17_0 26 cert72_layer_21_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 26 cert72_seen_21_17_1 = cert72_component_21_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_17_1 cert72_layer_21_17_1 25 cert72_layer_21_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 25 cert72_seen_21_17_2 = cert72_component_21_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_17_2 cert72_layer_21_17_2 24 cert72_layer_21_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 24 cert72_seen_21_17_3 = cert72_component_21_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_17_3 cert72_layer_21_17_3_eq 24

theorem cert72_step_21_17 :
    closedCollarIndexStepBool word fiber72 21 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_21_17)
    (by decide) (by decide)
    (by simpa [cert72_move_21_17] using cert72_component_21_17_eq)
    (by decide) (by decide) (by decide)

def cert72_move_21_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_21_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_21_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_21_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_21_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_37_0 = cert72_layer_21_37_0 := by
  decide

def cert72_seen_21_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_21_37_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_21_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_37_1 = cert72_layer_21_37_1 := by
  decide

def cert72_seen_21_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_21_37_2 : List ChainEdge :=
  []

theorem cert72_layer_21_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 21 [])
      LColor.b LColor.p cert72_seen_21_37_2 = cert72_layer_21_37_2 := by
  decide

theorem cert72_component_21_37_eq :
    closedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_21_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 27 cert72_seen_21_37_0 = cert72_component_21_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_37_0 cert72_layer_21_37_0 26 cert72_layer_21_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 26 cert72_seen_21_37_1 = cert72_component_21_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_37_1 cert72_layer_21_37_1 25 cert72_layer_21_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 21 [])
      LColor.b LColor.p 25 cert72_seen_21_37_2 = cert72_component_21_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 21 []) LColor.b LColor.p
    cert72_seen_21_37_2 cert72_layer_21_37_2_eq 25

theorem cert72_step_21_37 :
    closedCollarIndexStepBool word fiber72 21 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_21_37)
    (by decide) (by decide)
    (by simpa [cert72_move_21_37] using cert72_component_21_37_eq)
    (by decide) (by decide) (by decide)

def cert72_move_22_18 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_22_18 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_22_18_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_22_18_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_22_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_18_0 = cert72_layer_22_18_0 := by
  decide

def cert72_seen_22_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_22_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_22_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_18_1 = cert72_layer_22_18_1 := by
  decide

def cert72_seen_22_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_22_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_22_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_18_2 = cert72_layer_22_18_2 := by
  decide

def cert72_seen_22_18_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_22_18_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_22_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_18_3 = cert72_layer_22_18_3 := by
  decide

def cert72_seen_22_18_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_22_18_4 : List ChainEdge :=
  []

theorem cert72_layer_22_18_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_18_4 = cert72_layer_22_18_4 := by
  decide

theorem cert72_component_22_18_eq :
    closedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_22_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 22 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 27 cert72_seen_22_18_0 = cert72_component_22_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_18_0 cert72_layer_22_18_0 26 cert72_layer_22_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 26 cert72_seen_22_18_1 = cert72_component_22_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_18_1 cert72_layer_22_18_1 25 cert72_layer_22_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 25 cert72_seen_22_18_2 = cert72_component_22_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_18_2 cert72_layer_22_18_2 24 cert72_layer_22_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 24 cert72_seen_22_18_3 = cert72_component_22_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_18_3 cert72_layer_22_18_3 23 cert72_layer_22_18_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 23 cert72_seen_22_18_4 = cert72_component_22_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_18_4 cert72_layer_22_18_4_eq 23

theorem cert72_step_22_18 :
    closedCollarIndexStepBool word fiber72 22 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_22_18)
    (by decide) (by decide)
    (by simpa [cert72_move_22_18] using cert72_component_22_18_eq)
    (by decide) (by decide) (by decide)

def cert72_move_22_38 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_22_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_22_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_22_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_22_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_38_0 = cert72_layer_22_38_0 := by
  decide

def cert72_seen_22_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_22_38_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_22_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_38_1 = cert72_layer_22_38_1 := by
  decide

def cert72_seen_22_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_22_38_2 : List ChainEdge :=
  []

theorem cert72_layer_22_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 22 [])
      LColor.b LColor.p cert72_seen_22_38_2 = cert72_layer_22_38_2 := by
  decide

theorem cert72_component_22_38_eq :
    closedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_22_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 22 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 27 cert72_seen_22_38_0 = cert72_component_22_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_38_0 cert72_layer_22_38_0 26 cert72_layer_22_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 26 cert72_seen_22_38_1 = cert72_component_22_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_38_1 cert72_layer_22_38_1 25 cert72_layer_22_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 22 [])
      LColor.b LColor.p 25 cert72_seen_22_38_2 = cert72_component_22_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 22 []) LColor.b LColor.p
    cert72_seen_22_38_2 cert72_layer_22_38_2_eq 25

theorem cert72_step_22_38 :
    closedCollarIndexStepBool word fiber72 22 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_22_38)
    (by decide) (by decide)
    (by simpa [cert72_move_22_38] using cert72_component_22_38_eq)
    (by decide) (by decide) (by decide)

def cert72_move_23_20 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_23_20 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_23_20_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_23_20_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_23_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.r LColor.p cert72_seen_23_20_0 = cert72_layer_23_20_0 := by
  decide

def cert72_seen_23_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_23_20_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_23_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.r LColor.p cert72_seen_23_20_1 = cert72_layer_23_20_1 := by
  decide

def cert72_seen_23_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_23_20_2 : List ChainEdge :=
  []

theorem cert72_layer_23_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.r LColor.p cert72_seen_23_20_2 = cert72_layer_23_20_2 := by
  decide

theorem cert72_component_23_20_eq :
    closedCollarComponent word (listGetD fiber72 23 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_23_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 23 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.r LColor.p 27 cert72_seen_23_20_0 = cert72_component_23_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 23 []) LColor.r LColor.p
    cert72_seen_23_20_0 cert72_layer_23_20_0 26 cert72_layer_23_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.r LColor.p 26 cert72_seen_23_20_1 = cert72_component_23_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 23 []) LColor.r LColor.p
    cert72_seen_23_20_1 cert72_layer_23_20_1 25 cert72_layer_23_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.r LColor.p 25 cert72_seen_23_20_2 = cert72_component_23_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 23 []) LColor.r LColor.p
    cert72_seen_23_20_2 cert72_layer_23_20_2_eq 25

theorem cert72_step_23_20 :
    closedCollarIndexStepBool word fiber72 23 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_23_20)
    (by decide) (by decide)
    (by simpa [cert72_move_23_20] using cert72_component_23_20_eq)
    (by decide) (by decide) (by decide)

def cert72_move_23_39 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_23_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_23_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_23_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_23_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.b LColor.p cert72_seen_23_39_0 = cert72_layer_23_39_0 := by
  decide

def cert72_seen_23_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_23_39_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_23_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.b LColor.p cert72_seen_23_39_1 = cert72_layer_23_39_1 := by
  decide

def cert72_seen_23_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_23_39_2 : List ChainEdge :=
  []

theorem cert72_layer_23_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 23 [])
      LColor.b LColor.p cert72_seen_23_39_2 = cert72_layer_23_39_2 := by
  decide

theorem cert72_component_23_39_eq :
    closedCollarComponent word (listGetD fiber72 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_23_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 23 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.b LColor.p 27 cert72_seen_23_39_0 = cert72_component_23_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 23 []) LColor.b LColor.p
    cert72_seen_23_39_0 cert72_layer_23_39_0 26 cert72_layer_23_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.b LColor.p 26 cert72_seen_23_39_1 = cert72_component_23_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 23 []) LColor.b LColor.p
    cert72_seen_23_39_1 cert72_layer_23_39_1 25 cert72_layer_23_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 23 [])
      LColor.b LColor.p 25 cert72_seen_23_39_2 = cert72_component_23_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 23 []) LColor.b LColor.p
    cert72_seen_23_39_2 cert72_layer_23_39_2_eq 25

theorem cert72_step_23_39 :
    closedCollarIndexStepBool word fiber72 23 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_23_39)
    (by decide) (by decide)
    (by simpa [cert72_move_23_39] using cert72_component_23_39_eq)
    (by decide) (by decide) (by decide)

def cert72_move_24_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_24_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_24_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_24_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.r LColor.b cert72_seen_24_4_0 = cert72_layer_24_4_0 := by
  decide

def cert72_seen_24_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_24_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_24_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.r LColor.b cert72_seen_24_4_1 = cert72_layer_24_4_1 := by
  decide

def cert72_seen_24_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_24_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_24_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.r LColor.b cert72_seen_24_4_2 = cert72_layer_24_4_2 := by
  decide

def cert72_seen_24_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_24_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_24_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.r LColor.b cert72_seen_24_4_3 = cert72_layer_24_4_3 := by
  decide

def cert72_seen_24_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_24_4_4 : List ChainEdge :=
  []

theorem cert72_layer_24_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.r LColor.b cert72_seen_24_4_4 = cert72_layer_24_4_4 := by
  decide

theorem cert72_component_24_4_eq :
    closedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_24_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b 27 cert72_seen_24_4_0 = cert72_component_24_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.r LColor.b
    cert72_seen_24_4_0 cert72_layer_24_4_0 26 cert72_layer_24_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b 26 cert72_seen_24_4_1 = cert72_component_24_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.r LColor.b
    cert72_seen_24_4_1 cert72_layer_24_4_1 25 cert72_layer_24_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b 25 cert72_seen_24_4_2 = cert72_component_24_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.r LColor.b
    cert72_seen_24_4_2 cert72_layer_24_4_2 24 cert72_layer_24_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b 24 cert72_seen_24_4_3 = cert72_component_24_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.r LColor.b
    cert72_seen_24_4_3 cert72_layer_24_4_3 23 cert72_layer_24_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.r LColor.b 23 cert72_seen_24_4_4 = cert72_component_24_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 24 []) LColor.r LColor.b
    cert72_seen_24_4_4 cert72_layer_24_4_4_eq 23

theorem cert72_step_24_4 :
    closedCollarIndexStepBool word fiber72 24 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_24_4)
    (by decide) (by decide)
    (by simpa [cert72_move_24_4] using cert72_component_24_4_eq)
    (by decide) (by decide) (by decide)

def cert72_move_24_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_24_28 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_24_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_24_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_24_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.b LColor.p cert72_seen_24_28_0 = cert72_layer_24_28_0 := by
  decide

def cert72_seen_24_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_24_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_24_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.b LColor.p cert72_seen_24_28_1 = cert72_layer_24_28_1 := by
  decide

def cert72_seen_24_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_24_28_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_24_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.b LColor.p cert72_seen_24_28_2 = cert72_layer_24_28_2 := by
  decide

def cert72_seen_24_28_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_24_28_3 : List ChainEdge :=
  []

theorem cert72_layer_24_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 24 [])
      LColor.b LColor.p cert72_seen_24_28_3 = cert72_layer_24_28_3 := by
  decide

theorem cert72_component_24_28_eq :
    closedCollarComponent word (listGetD fiber72 24 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_24_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 24 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.b LColor.p 27 cert72_seen_24_28_0 = cert72_component_24_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.b LColor.p
    cert72_seen_24_28_0 cert72_layer_24_28_0 26 cert72_layer_24_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.b LColor.p 26 cert72_seen_24_28_1 = cert72_component_24_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.b LColor.p
    cert72_seen_24_28_1 cert72_layer_24_28_1 25 cert72_layer_24_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.b LColor.p 25 cert72_seen_24_28_2 = cert72_component_24_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 24 []) LColor.b LColor.p
    cert72_seen_24_28_2 cert72_layer_24_28_2 24 cert72_layer_24_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 24 [])
      LColor.b LColor.p 24 cert72_seen_24_28_3 = cert72_component_24_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 24 []) LColor.b LColor.p
    cert72_seen_24_28_3 cert72_layer_24_28_3_eq 24

theorem cert72_step_24_28 :
    closedCollarIndexStepBool word fiber72 24 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_24_28)
    (by decide) (by decide)
    (by simpa [cert72_move_24_28] using cert72_component_24_28_eq)
    (by decide) (by decide) (by decide)

def cert72_move_25_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_25_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_25_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_25_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_25_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.r LColor.b cert72_seen_25_5_0 = cert72_layer_25_5_0 := by
  decide

def cert72_seen_25_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_25_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_25_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.r LColor.b cert72_seen_25_5_1 = cert72_layer_25_5_1 := by
  decide

def cert72_seen_25_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_25_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_25_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.r LColor.b cert72_seen_25_5_2 = cert72_layer_25_5_2 := by
  decide

def cert72_seen_25_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_25_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_25_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.r LColor.b cert72_seen_25_5_3 = cert72_layer_25_5_3 := by
  decide

def cert72_seen_25_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_25_5_4 : List ChainEdge :=
  []

theorem cert72_layer_25_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.r LColor.b cert72_seen_25_5_4 = cert72_layer_25_5_4 := by
  decide

theorem cert72_component_25_5_eq :
    closedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_25_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b 27 cert72_seen_25_5_0 = cert72_component_25_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.r LColor.b
    cert72_seen_25_5_0 cert72_layer_25_5_0 26 cert72_layer_25_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b 26 cert72_seen_25_5_1 = cert72_component_25_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.r LColor.b
    cert72_seen_25_5_1 cert72_layer_25_5_1 25 cert72_layer_25_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b 25 cert72_seen_25_5_2 = cert72_component_25_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.r LColor.b
    cert72_seen_25_5_2 cert72_layer_25_5_2 24 cert72_layer_25_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b 24 cert72_seen_25_5_3 = cert72_component_25_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.r LColor.b
    cert72_seen_25_5_3 cert72_layer_25_5_3 23 cert72_layer_25_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.r LColor.b 23 cert72_seen_25_5_4 = cert72_component_25_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 25 []) LColor.r LColor.b
    cert72_seen_25_5_4 cert72_layer_25_5_4_eq 23

theorem cert72_step_25_5 :
    closedCollarIndexStepBool word fiber72 25 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_25_5)
    (by decide) (by decide)
    (by simpa [cert72_move_25_5] using cert72_component_25_5_eq)
    (by decide) (by decide) (by decide)

def cert72_move_25_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_25_29 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_25_29_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_25_29_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_25_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.b LColor.p cert72_seen_25_29_0 = cert72_layer_25_29_0 := by
  decide

def cert72_seen_25_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_25_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_25_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.b LColor.p cert72_seen_25_29_1 = cert72_layer_25_29_1 := by
  decide

def cert72_seen_25_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_25_29_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_25_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.b LColor.p cert72_seen_25_29_2 = cert72_layer_25_29_2 := by
  decide

def cert72_seen_25_29_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_25_29_3 : List ChainEdge :=
  []

theorem cert72_layer_25_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 25 [])
      LColor.b LColor.p cert72_seen_25_29_3 = cert72_layer_25_29_3 := by
  decide

theorem cert72_component_25_29_eq :
    closedCollarComponent word (listGetD fiber72 25 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_25_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 25 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.b LColor.p 27 cert72_seen_25_29_0 = cert72_component_25_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.b LColor.p
    cert72_seen_25_29_0 cert72_layer_25_29_0 26 cert72_layer_25_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.b LColor.p 26 cert72_seen_25_29_1 = cert72_component_25_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.b LColor.p
    cert72_seen_25_29_1 cert72_layer_25_29_1 25 cert72_layer_25_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.b LColor.p 25 cert72_seen_25_29_2 = cert72_component_25_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 25 []) LColor.b LColor.p
    cert72_seen_25_29_2 cert72_layer_25_29_2 24 cert72_layer_25_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 25 [])
      LColor.b LColor.p 24 cert72_seen_25_29_3 = cert72_component_25_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 25 []) LColor.b LColor.p
    cert72_seen_25_29_3 cert72_layer_25_29_3_eq 24

theorem cert72_step_25_29 :
    closedCollarIndexStepBool word fiber72 25 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_25_29)
    (by decide) (by decide)
    (by simpa [cert72_move_25_29] using cert72_component_25_29_eq)
    (by decide) (by decide) (by decide)

def cert72_move_26_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_26_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_26_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_26_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_26_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.r LColor.b cert72_seen_26_6_0 = cert72_layer_26_6_0 := by
  decide

def cert72_seen_26_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_26_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_26_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.r LColor.b cert72_seen_26_6_1 = cert72_layer_26_6_1 := by
  decide

def cert72_seen_26_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_26_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_26_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.r LColor.b cert72_seen_26_6_2 = cert72_layer_26_6_2 := by
  decide

def cert72_seen_26_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_26_6_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_26_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.r LColor.b cert72_seen_26_6_3 = cert72_layer_26_6_3 := by
  decide

def cert72_seen_26_6_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_26_6_4 : List ChainEdge :=
  []

theorem cert72_layer_26_6_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.r LColor.b cert72_seen_26_6_4 = cert72_layer_26_6_4 := by
  decide

theorem cert72_component_26_6_eq :
    closedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_26_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b 27 cert72_seen_26_6_0 = cert72_component_26_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.r LColor.b
    cert72_seen_26_6_0 cert72_layer_26_6_0 26 cert72_layer_26_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b 26 cert72_seen_26_6_1 = cert72_component_26_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.r LColor.b
    cert72_seen_26_6_1 cert72_layer_26_6_1 25 cert72_layer_26_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b 25 cert72_seen_26_6_2 = cert72_component_26_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.r LColor.b
    cert72_seen_26_6_2 cert72_layer_26_6_2 24 cert72_layer_26_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b 24 cert72_seen_26_6_3 = cert72_component_26_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.r LColor.b
    cert72_seen_26_6_3 cert72_layer_26_6_3 23 cert72_layer_26_6_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.r LColor.b 23 cert72_seen_26_6_4 = cert72_component_26_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 26 []) LColor.r LColor.b
    cert72_seen_26_6_4 cert72_layer_26_6_4_eq 23

theorem cert72_step_26_6 :
    closedCollarIndexStepBool word fiber72 26 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_26_6)
    (by decide) (by decide)
    (by simpa [cert72_move_26_6] using cert72_component_26_6_eq)
    (by decide) (by decide) (by decide)

def cert72_move_26_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_26_30 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_26_30_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_26_30_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_26_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.b LColor.p cert72_seen_26_30_0 = cert72_layer_26_30_0 := by
  decide

def cert72_seen_26_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_26_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_26_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.b LColor.p cert72_seen_26_30_1 = cert72_layer_26_30_1 := by
  decide

def cert72_seen_26_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_26_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_26_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.b LColor.p cert72_seen_26_30_2 = cert72_layer_26_30_2 := by
  decide

def cert72_seen_26_30_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_26_30_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_26_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.b LColor.p cert72_seen_26_30_3 = cert72_layer_26_30_3 := by
  decide

def cert72_seen_26_30_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_26_30_4 : List ChainEdge :=
  []

theorem cert72_layer_26_30_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 26 [])
      LColor.b LColor.p cert72_seen_26_30_4 = cert72_layer_26_30_4 := by
  decide

theorem cert72_component_26_30_eq :
    closedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_26_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 26 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p 27 cert72_seen_26_30_0 = cert72_component_26_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.b LColor.p
    cert72_seen_26_30_0 cert72_layer_26_30_0 26 cert72_layer_26_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p 26 cert72_seen_26_30_1 = cert72_component_26_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.b LColor.p
    cert72_seen_26_30_1 cert72_layer_26_30_1 25 cert72_layer_26_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p 25 cert72_seen_26_30_2 = cert72_component_26_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.b LColor.p
    cert72_seen_26_30_2 cert72_layer_26_30_2 24 cert72_layer_26_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p 24 cert72_seen_26_30_3 = cert72_component_26_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 26 []) LColor.b LColor.p
    cert72_seen_26_30_3 cert72_layer_26_30_3 23 cert72_layer_26_30_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 26 [])
      LColor.b LColor.p 23 cert72_seen_26_30_4 = cert72_component_26_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 26 []) LColor.b LColor.p
    cert72_seen_26_30_4 cert72_layer_26_30_4_eq 23

theorem cert72_step_26_30 :
    closedCollarIndexStepBool word fiber72 26 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_26_30)
    (by decide) (by decide)
    (by simpa [cert72_move_26_30] using cert72_component_26_30_eq)
    (by decide) (by decide) (by decide)

def cert72_move_27_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_27_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_27_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_27_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_27_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 27 [])
      LColor.r LColor.b cert72_seen_27_7_0 = cert72_layer_27_7_0 := by
  decide

def cert72_seen_27_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_27_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_27_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 27 [])
      LColor.r LColor.b cert72_seen_27_7_1 = cert72_layer_27_7_1 := by
  decide

def cert72_seen_27_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_27_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_27_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 27 [])
      LColor.r LColor.b cert72_seen_27_7_2 = cert72_layer_27_7_2 := by
  decide

def cert72_seen_27_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_27_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_27_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 27 [])
      LColor.r LColor.b cert72_seen_27_7_3 = cert72_layer_27_7_3 := by
  decide

def cert72_seen_27_7_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_27_7_4 : List ChainEdge :=
  []

theorem cert72_layer_27_7_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 27 [])
      LColor.r LColor.b cert72_seen_27_7_4 = cert72_layer_27_7_4 := by
  decide

theorem cert72_component_27_7_eq :
    closedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_27_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b 27 cert72_seen_27_7_0 = cert72_component_27_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 27 []) LColor.r LColor.b
    cert72_seen_27_7_0 cert72_layer_27_7_0 26 cert72_layer_27_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b 26 cert72_seen_27_7_1 = cert72_component_27_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 27 []) LColor.r LColor.b
    cert72_seen_27_7_1 cert72_layer_27_7_1 25 cert72_layer_27_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b 25 cert72_seen_27_7_2 = cert72_component_27_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 27 []) LColor.r LColor.b
    cert72_seen_27_7_2 cert72_layer_27_7_2 24 cert72_layer_27_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b 24 cert72_seen_27_7_3 = cert72_component_27_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 27 []) LColor.r LColor.b
    cert72_seen_27_7_3 cert72_layer_27_7_3 23 cert72_layer_27_7_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 27 [])
      LColor.r LColor.b 23 cert72_seen_27_7_4 = cert72_component_27_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 27 []) LColor.r LColor.b
    cert72_seen_27_7_4 cert72_layer_27_7_4_eq 23

theorem cert72_step_27_7 :
    closedCollarIndexStepBool word fiber72 27 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_27_7)
    (by decide) (by decide)
    (by simpa [cert72_move_27_7] using cert72_component_27_7_eq)
    (by decide) (by decide) (by decide)

def cert72_move_28_24 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_28_24 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_28_24_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_28_24_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_28_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.b LColor.p cert72_seen_28_24_0 = cert72_layer_28_24_0 := by
  decide

def cert72_seen_28_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_28_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_28_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.b LColor.p cert72_seen_28_24_1 = cert72_layer_28_24_1 := by
  decide

def cert72_seen_28_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_28_24_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_28_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.b LColor.p cert72_seen_28_24_2 = cert72_layer_28_24_2 := by
  decide

def cert72_seen_28_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_28_24_3 : List ChainEdge :=
  []

theorem cert72_layer_28_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.b LColor.p cert72_seen_28_24_3 = cert72_layer_28_24_3 := by
  decide

theorem cert72_component_28_24_eq :
    closedCollarComponent word (listGetD fiber72 28 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_28_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 28 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.b LColor.p 27 cert72_seen_28_24_0 = cert72_component_28_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 28 []) LColor.b LColor.p
    cert72_seen_28_24_0 cert72_layer_28_24_0 26 cert72_layer_28_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.b LColor.p 26 cert72_seen_28_24_1 = cert72_component_28_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 28 []) LColor.b LColor.p
    cert72_seen_28_24_1 cert72_layer_28_24_1 25 cert72_layer_28_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.b LColor.p 25 cert72_seen_28_24_2 = cert72_component_28_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 28 []) LColor.b LColor.p
    cert72_seen_28_24_2 cert72_layer_28_24_2 24 cert72_layer_28_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.b LColor.p 24 cert72_seen_28_24_3 = cert72_component_28_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 28 []) LColor.b LColor.p
    cert72_seen_28_24_3 cert72_layer_28_24_3_eq 24

theorem cert72_step_28_24 :
    closedCollarIndexStepBool word fiber72 28 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_28_24)
    (by decide) (by decide)
    (by simpa [cert72_move_28_24] using cert72_component_28_24_eq)
    (by decide) (by decide) (by decide)

def cert72_move_28_31 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_28_31 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_28_31_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_28_31_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_28_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.r LColor.p cert72_seen_28_31_0 = cert72_layer_28_31_0 := by
  decide

def cert72_seen_28_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_28_31_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_28_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.r LColor.p cert72_seen_28_31_1 = cert72_layer_28_31_1 := by
  decide

def cert72_seen_28_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_28_31_2 : List ChainEdge :=
  []

theorem cert72_layer_28_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 28 [])
      LColor.r LColor.p cert72_seen_28_31_2 = cert72_layer_28_31_2 := by
  decide

theorem cert72_component_28_31_eq :
    closedCollarComponent word (listGetD fiber72 28 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_28_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 28 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.r LColor.p 27 cert72_seen_28_31_0 = cert72_component_28_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 28 []) LColor.r LColor.p
    cert72_seen_28_31_0 cert72_layer_28_31_0 26 cert72_layer_28_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.r LColor.p 26 cert72_seen_28_31_1 = cert72_component_28_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 28 []) LColor.r LColor.p
    cert72_seen_28_31_1 cert72_layer_28_31_1 25 cert72_layer_28_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 28 [])
      LColor.r LColor.p 25 cert72_seen_28_31_2 = cert72_component_28_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 28 []) LColor.r LColor.p
    cert72_seen_28_31_2 cert72_layer_28_31_2_eq 25

theorem cert72_step_28_31 :
    closedCollarIndexStepBool word fiber72 28 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_28_31)
    (by decide) (by decide)
    (by simpa [cert72_move_28_31] using cert72_component_28_31_eq)
    (by decide) (by decide) (by decide)

def cert72_move_29_25 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_29_25 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_29_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_29_25_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_29_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 29 [])
      LColor.b LColor.p cert72_seen_29_25_0 = cert72_layer_29_25_0 := by
  decide

def cert72_seen_29_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_29_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_29_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 29 [])
      LColor.b LColor.p cert72_seen_29_25_1 = cert72_layer_29_25_1 := by
  decide

def cert72_seen_29_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_29_25_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_29_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 29 [])
      LColor.b LColor.p cert72_seen_29_25_2 = cert72_layer_29_25_2 := by
  decide

def cert72_seen_29_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_29_25_3 : List ChainEdge :=
  []

theorem cert72_layer_29_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 29 [])
      LColor.b LColor.p cert72_seen_29_25_3 = cert72_layer_29_25_3 := by
  decide

theorem cert72_component_29_25_eq :
    closedCollarComponent word (listGetD fiber72 29 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_29_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 29 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 29 [])
      LColor.b LColor.p 27 cert72_seen_29_25_0 = cert72_component_29_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 29 []) LColor.b LColor.p
    cert72_seen_29_25_0 cert72_layer_29_25_0 26 cert72_layer_29_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 29 [])
      LColor.b LColor.p 26 cert72_seen_29_25_1 = cert72_component_29_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 29 []) LColor.b LColor.p
    cert72_seen_29_25_1 cert72_layer_29_25_1 25 cert72_layer_29_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 29 [])
      LColor.b LColor.p 25 cert72_seen_29_25_2 = cert72_component_29_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 29 []) LColor.b LColor.p
    cert72_seen_29_25_2 cert72_layer_29_25_2 24 cert72_layer_29_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 29 [])
      LColor.b LColor.p 24 cert72_seen_29_25_3 = cert72_component_29_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 29 []) LColor.b LColor.p
    cert72_seen_29_25_3 cert72_layer_29_25_3_eq 24

theorem cert72_step_29_25 :
    closedCollarIndexStepBool word fiber72 29 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_29_25)
    (by decide) (by decide)
    (by simpa [cert72_move_29_25] using cert72_component_29_25_eq)
    (by decide) (by decide) (by decide)

def cert72_move_30_26 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_30_26 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_30_26_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_30_26_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_30_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 30 [])
      LColor.b LColor.p cert72_seen_30_26_0 = cert72_layer_30_26_0 := by
  decide

def cert72_seen_30_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_30_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_30_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 30 [])
      LColor.b LColor.p cert72_seen_30_26_1 = cert72_layer_30_26_1 := by
  decide

def cert72_seen_30_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_30_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_30_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 30 [])
      LColor.b LColor.p cert72_seen_30_26_2 = cert72_layer_30_26_2 := by
  decide

def cert72_seen_30_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_30_26_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_30_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 30 [])
      LColor.b LColor.p cert72_seen_30_26_3 = cert72_layer_30_26_3 := by
  decide

def cert72_seen_30_26_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_30_26_4 : List ChainEdge :=
  []

theorem cert72_layer_30_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 30 [])
      LColor.b LColor.p cert72_seen_30_26_4 = cert72_layer_30_26_4 := by
  decide

theorem cert72_component_30_26_eq :
    closedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_30_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 30 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p 27 cert72_seen_30_26_0 = cert72_component_30_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 30 []) LColor.b LColor.p
    cert72_seen_30_26_0 cert72_layer_30_26_0 26 cert72_layer_30_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p 26 cert72_seen_30_26_1 = cert72_component_30_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 30 []) LColor.b LColor.p
    cert72_seen_30_26_1 cert72_layer_30_26_1 25 cert72_layer_30_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p 25 cert72_seen_30_26_2 = cert72_component_30_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 30 []) LColor.b LColor.p
    cert72_seen_30_26_2 cert72_layer_30_26_2 24 cert72_layer_30_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p 24 cert72_seen_30_26_3 = cert72_component_30_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 30 []) LColor.b LColor.p
    cert72_seen_30_26_3 cert72_layer_30_26_3 23 cert72_layer_30_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 30 [])
      LColor.b LColor.p 23 cert72_seen_30_26_4 = cert72_component_30_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 30 []) LColor.b LColor.p
    cert72_seen_30_26_4 cert72_layer_30_26_4_eq 23

theorem cert72_step_30_26 :
    closedCollarIndexStepBool word fiber72 30 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_30_26)
    (by decide) (by decide)
    (by simpa [cert72_move_30_26] using cert72_component_30_26_eq)
    (by decide) (by decide) (by decide)

def cert72_move_31_28 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_31_28 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_31_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_31_28_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_31_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 31 [])
      LColor.r LColor.p cert72_seen_31_28_0 = cert72_layer_31_28_0 := by
  decide

def cert72_seen_31_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_31_28_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_31_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 31 [])
      LColor.r LColor.p cert72_seen_31_28_1 = cert72_layer_31_28_1 := by
  decide

def cert72_seen_31_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_31_28_2 : List ChainEdge :=
  []

theorem cert72_layer_31_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 31 [])
      LColor.r LColor.p cert72_seen_31_28_2 = cert72_layer_31_28_2 := by
  decide

theorem cert72_component_31_28_eq :
    closedCollarComponent word (listGetD fiber72 31 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_31_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 31 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 31 [])
      LColor.r LColor.p 27 cert72_seen_31_28_0 = cert72_component_31_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 31 []) LColor.r LColor.p
    cert72_seen_31_28_0 cert72_layer_31_28_0 26 cert72_layer_31_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 31 [])
      LColor.r LColor.p 26 cert72_seen_31_28_1 = cert72_component_31_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 31 []) LColor.r LColor.p
    cert72_seen_31_28_1 cert72_layer_31_28_1 25 cert72_layer_31_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 31 [])
      LColor.r LColor.p 25 cert72_seen_31_28_2 = cert72_component_31_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 31 []) LColor.r LColor.p
    cert72_seen_31_28_2 cert72_layer_31_28_2_eq 25

theorem cert72_step_31_28 :
    closedCollarIndexStepBool word fiber72 31 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_31_28)
    (by decide) (by decide)
    (by simpa [cert72_move_31_28] using cert72_component_31_28_eq)
    (by decide) (by decide) (by decide)

def cert72_move_32_16 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_32_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_32_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_32_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_32_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 32 [])
      LColor.b LColor.p cert72_seen_32_16_0 = cert72_layer_32_16_0 := by
  decide

def cert72_seen_32_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_32_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_32_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 32 [])
      LColor.b LColor.p cert72_seen_32_16_1 = cert72_layer_32_16_1 := by
  decide

def cert72_seen_32_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_32_16_2 : List ChainEdge :=
  []

theorem cert72_layer_32_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 32 [])
      LColor.b LColor.p cert72_seen_32_16_2 = cert72_layer_32_16_2 := by
  decide

theorem cert72_component_32_16_eq :
    closedCollarComponent word (listGetD fiber72 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_32_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 32 [])
      LColor.b LColor.p 27 cert72_seen_32_16_0 = cert72_component_32_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 32 []) LColor.b LColor.p
    cert72_seen_32_16_0 cert72_layer_32_16_0 26 cert72_layer_32_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 32 [])
      LColor.b LColor.p 26 cert72_seen_32_16_1 = cert72_component_32_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 32 []) LColor.b LColor.p
    cert72_seen_32_16_1 cert72_layer_32_16_1 25 cert72_layer_32_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 32 [])
      LColor.b LColor.p 25 cert72_seen_32_16_2 = cert72_component_32_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 32 []) LColor.b LColor.p
    cert72_seen_32_16_2 cert72_layer_32_16_2_eq 25

theorem cert72_step_32_16 :
    closedCollarIndexStepBool word fiber72 32 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_32_16)
    (by decide) (by decide)
    (by simpa [cert72_move_32_16] using cert72_component_32_16_eq)
    (by decide) (by decide) (by decide)

def cert72_move_33_17 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_33_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_33_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_33_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_33_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 33 [])
      LColor.b LColor.p cert72_seen_33_17_0 = cert72_layer_33_17_0 := by
  decide

def cert72_seen_33_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_33_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_33_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 33 [])
      LColor.b LColor.p cert72_seen_33_17_1 = cert72_layer_33_17_1 := by
  decide

def cert72_seen_33_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_33_17_2 : List ChainEdge :=
  []

theorem cert72_layer_33_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 33 [])
      LColor.b LColor.p cert72_seen_33_17_2 = cert72_layer_33_17_2 := by
  decide

theorem cert72_component_33_17_eq :
    closedCollarComponent word (listGetD fiber72 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_33_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 33 [])
      LColor.b LColor.p 27 cert72_seen_33_17_0 = cert72_component_33_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 33 []) LColor.b LColor.p
    cert72_seen_33_17_0 cert72_layer_33_17_0 26 cert72_layer_33_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 33 [])
      LColor.b LColor.p 26 cert72_seen_33_17_1 = cert72_component_33_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 33 []) LColor.b LColor.p
    cert72_seen_33_17_1 cert72_layer_33_17_1 25 cert72_layer_33_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 33 [])
      LColor.b LColor.p 25 cert72_seen_33_17_2 = cert72_component_33_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 33 []) LColor.b LColor.p
    cert72_seen_33_17_2 cert72_layer_33_17_2_eq 25

theorem cert72_step_33_17 :
    closedCollarIndexStepBool word fiber72 33 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_33_17)
    (by decide) (by decide)
    (by simpa [cert72_move_33_17] using cert72_component_33_17_eq)
    (by decide) (by decide) (by decide)

def cert72_move_34_18 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_34_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_34_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_34_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_34_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 34 [])
      LColor.b LColor.p cert72_seen_34_18_0 = cert72_layer_34_18_0 := by
  decide

def cert72_seen_34_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_34_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_34_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 34 [])
      LColor.b LColor.p cert72_seen_34_18_1 = cert72_layer_34_18_1 := by
  decide

def cert72_seen_34_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_34_18_2 : List ChainEdge :=
  []

theorem cert72_layer_34_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 34 [])
      LColor.b LColor.p cert72_seen_34_18_2 = cert72_layer_34_18_2 := by
  decide

theorem cert72_component_34_18_eq :
    closedCollarComponent word (listGetD fiber72 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_34_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 34 [])
      LColor.b LColor.p 27 cert72_seen_34_18_0 = cert72_component_34_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 34 []) LColor.b LColor.p
    cert72_seen_34_18_0 cert72_layer_34_18_0 26 cert72_layer_34_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 34 [])
      LColor.b LColor.p 26 cert72_seen_34_18_1 = cert72_component_34_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 34 []) LColor.b LColor.p
    cert72_seen_34_18_1 cert72_layer_34_18_1 25 cert72_layer_34_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 34 [])
      LColor.b LColor.p 25 cert72_seen_34_18_2 = cert72_component_34_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 34 []) LColor.b LColor.p
    cert72_seen_34_18_2 cert72_layer_34_18_2_eq 25

theorem cert72_step_34_18 :
    closedCollarIndexStepBool word fiber72 34 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_34_18)
    (by decide) (by decide)
    (by simpa [cert72_move_34_18] using cert72_component_34_18_eq)
    (by decide) (by decide) (by decide)

def cert72_move_35_19 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_35_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_35_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_35_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_35_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 35 [])
      LColor.b LColor.p cert72_seen_35_19_0 = cert72_layer_35_19_0 := by
  decide

def cert72_seen_35_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_35_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_35_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 35 [])
      LColor.b LColor.p cert72_seen_35_19_1 = cert72_layer_35_19_1 := by
  decide

def cert72_seen_35_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_35_19_2 : List ChainEdge :=
  []

theorem cert72_layer_35_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 35 [])
      LColor.b LColor.p cert72_seen_35_19_2 = cert72_layer_35_19_2 := by
  decide

theorem cert72_component_35_19_eq :
    closedCollarComponent word (listGetD fiber72 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_35_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 35 [])
      LColor.b LColor.p 27 cert72_seen_35_19_0 = cert72_component_35_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 35 []) LColor.b LColor.p
    cert72_seen_35_19_0 cert72_layer_35_19_0 26 cert72_layer_35_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 35 [])
      LColor.b LColor.p 26 cert72_seen_35_19_1 = cert72_component_35_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 35 []) LColor.b LColor.p
    cert72_seen_35_19_1 cert72_layer_35_19_1 25 cert72_layer_35_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 35 [])
      LColor.b LColor.p 25 cert72_seen_35_19_2 = cert72_component_35_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 35 []) LColor.b LColor.p
    cert72_seen_35_19_2 cert72_layer_35_19_2_eq 25

theorem cert72_step_35_19 :
    closedCollarIndexStepBool word fiber72 35 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_35_19)
    (by decide) (by decide)
    (by simpa [cert72_move_35_19] using cert72_component_35_19_eq)
    (by decide) (by decide) (by decide)

def cert72_move_36_20 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_36_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_36_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_36_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_36_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 36 [])
      LColor.b LColor.p cert72_seen_36_20_0 = cert72_layer_36_20_0 := by
  decide

def cert72_seen_36_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_36_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_36_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 36 [])
      LColor.b LColor.p cert72_seen_36_20_1 = cert72_layer_36_20_1 := by
  decide

def cert72_seen_36_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_36_20_2 : List ChainEdge :=
  []

theorem cert72_layer_36_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 36 [])
      LColor.b LColor.p cert72_seen_36_20_2 = cert72_layer_36_20_2 := by
  decide

theorem cert72_component_36_20_eq :
    closedCollarComponent word (listGetD fiber72 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_36_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 36 [])
      LColor.b LColor.p 27 cert72_seen_36_20_0 = cert72_component_36_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 36 []) LColor.b LColor.p
    cert72_seen_36_20_0 cert72_layer_36_20_0 26 cert72_layer_36_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 36 [])
      LColor.b LColor.p 26 cert72_seen_36_20_1 = cert72_component_36_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 36 []) LColor.b LColor.p
    cert72_seen_36_20_1 cert72_layer_36_20_1 25 cert72_layer_36_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 36 [])
      LColor.b LColor.p 25 cert72_seen_36_20_2 = cert72_component_36_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 36 []) LColor.b LColor.p
    cert72_seen_36_20_2 cert72_layer_36_20_2_eq 25

theorem cert72_step_36_20 :
    closedCollarIndexStepBool word fiber72 36 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_36_20)
    (by decide) (by decide)
    (by simpa [cert72_move_36_20] using cert72_component_36_20_eq)
    (by decide) (by decide) (by decide)

def cert72_move_37_21 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_37_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_37_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_37_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_37_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 37 [])
      LColor.b LColor.p cert72_seen_37_21_0 = cert72_layer_37_21_0 := by
  decide

def cert72_seen_37_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_37_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_37_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 37 [])
      LColor.b LColor.p cert72_seen_37_21_1 = cert72_layer_37_21_1 := by
  decide

def cert72_seen_37_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_37_21_2 : List ChainEdge :=
  []

theorem cert72_layer_37_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 37 [])
      LColor.b LColor.p cert72_seen_37_21_2 = cert72_layer_37_21_2 := by
  decide

theorem cert72_component_37_21_eq :
    closedCollarComponent word (listGetD fiber72 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_37_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 37 [])
      LColor.b LColor.p 27 cert72_seen_37_21_0 = cert72_component_37_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 37 []) LColor.b LColor.p
    cert72_seen_37_21_0 cert72_layer_37_21_0 26 cert72_layer_37_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 37 [])
      LColor.b LColor.p 26 cert72_seen_37_21_1 = cert72_component_37_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 37 []) LColor.b LColor.p
    cert72_seen_37_21_1 cert72_layer_37_21_1 25 cert72_layer_37_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 37 [])
      LColor.b LColor.p 25 cert72_seen_37_21_2 = cert72_component_37_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 37 []) LColor.b LColor.p
    cert72_seen_37_21_2 cert72_layer_37_21_2_eq 25

theorem cert72_step_37_21 :
    closedCollarIndexStepBool word fiber72 37 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_37_21)
    (by decide) (by decide)
    (by simpa [cert72_move_37_21] using cert72_component_37_21_eq)
    (by decide) (by decide) (by decide)

def cert72_move_38_22 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_38_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_38_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_38_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_38_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 38 [])
      LColor.b LColor.p cert72_seen_38_22_0 = cert72_layer_38_22_0 := by
  decide

def cert72_seen_38_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_38_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_38_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 38 [])
      LColor.b LColor.p cert72_seen_38_22_1 = cert72_layer_38_22_1 := by
  decide

def cert72_seen_38_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_38_22_2 : List ChainEdge :=
  []

theorem cert72_layer_38_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 38 [])
      LColor.b LColor.p cert72_seen_38_22_2 = cert72_layer_38_22_2 := by
  decide

theorem cert72_component_38_22_eq :
    closedCollarComponent word (listGetD fiber72 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_38_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 38 [])
      LColor.b LColor.p 27 cert72_seen_38_22_0 = cert72_component_38_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 38 []) LColor.b LColor.p
    cert72_seen_38_22_0 cert72_layer_38_22_0 26 cert72_layer_38_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 38 [])
      LColor.b LColor.p 26 cert72_seen_38_22_1 = cert72_component_38_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 38 []) LColor.b LColor.p
    cert72_seen_38_22_1 cert72_layer_38_22_1 25 cert72_layer_38_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 38 [])
      LColor.b LColor.p 25 cert72_seen_38_22_2 = cert72_component_38_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 38 []) LColor.b LColor.p
    cert72_seen_38_22_2 cert72_layer_38_22_2_eq 25

theorem cert72_step_38_22 :
    closedCollarIndexStepBool word fiber72 38 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_38_22)
    (by decide) (by decide)
    (by simpa [cert72_move_38_22] using cert72_component_38_22_eq)
    (by decide) (by decide) (by decide)

def cert72_move_39_23 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert72_component_39_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_seen_39_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert72_layer_39_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert72_layer_39_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 39 [])
      LColor.b LColor.p cert72_seen_39_23_0 = cert72_layer_39_23_0 := by
  decide

def cert72_seen_39_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert72_layer_39_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert72_layer_39_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 39 [])
      LColor.b LColor.p cert72_seen_39_23_1 = cert72_layer_39_23_1 := by
  decide

def cert72_seen_39_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert72_layer_39_23_2 : List ChainEdge :=
  []

theorem cert72_layer_39_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 39 [])
      LColor.b LColor.p cert72_seen_39_23_2 = cert72_layer_39_23_2 := by
  decide

theorem cert72_component_39_23_eq :
    closedCollarComponent word (listGetD fiber72 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert72_component_39_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 39 [])
      LColor.b LColor.p 27 cert72_seen_39_23_0 = cert72_component_39_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 39 []) LColor.b LColor.p
    cert72_seen_39_23_0 cert72_layer_39_23_0 26 cert72_layer_39_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 39 [])
      LColor.b LColor.p 26 cert72_seen_39_23_1 = cert72_component_39_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 39 []) LColor.b LColor.p
    cert72_seen_39_23_1 cert72_layer_39_23_1 25 cert72_layer_39_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 39 [])
      LColor.b LColor.p 25 cert72_seen_39_23_2 = cert72_component_39_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 39 []) LColor.b LColor.p
    cert72_seen_39_23_2 cert72_layer_39_23_2_eq 25

theorem cert72_step_39_23 :
    closedCollarIndexStepBool word fiber72 39 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_39_23)
    (by decide) (by decide)
    (by simpa [cert72_move_39_23] using cert72_component_39_23_eq)
    (by decide) (by decide) (by decide)

def cert72_move_40_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_40_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_40_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_40_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_40_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.r LColor.b cert72_seen_40_12_0 = cert72_layer_40_12_0 := by
  decide

def cert72_seen_40_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_40_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_40_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.r LColor.b cert72_seen_40_12_1 = cert72_layer_40_12_1 := by
  decide

def cert72_seen_40_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_40_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_40_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.r LColor.b cert72_seen_40_12_2 = cert72_layer_40_12_2 := by
  decide

def cert72_seen_40_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_40_12_3 : List ChainEdge :=
  []

theorem cert72_layer_40_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.r LColor.b cert72_seen_40_12_3 = cert72_layer_40_12_3 := by
  decide

theorem cert72_component_40_12_eq :
    closedCollarComponent word (listGetD fiber72 40 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_40_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 40 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.r LColor.b 27 cert72_seen_40_12_0 = cert72_component_40_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.r LColor.b
    cert72_seen_40_12_0 cert72_layer_40_12_0 26 cert72_layer_40_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.r LColor.b 26 cert72_seen_40_12_1 = cert72_component_40_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.r LColor.b
    cert72_seen_40_12_1 cert72_layer_40_12_1 25 cert72_layer_40_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.r LColor.b 25 cert72_seen_40_12_2 = cert72_component_40_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.r LColor.b
    cert72_seen_40_12_2 cert72_layer_40_12_2 24 cert72_layer_40_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.r LColor.b 24 cert72_seen_40_12_3 = cert72_component_40_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 40 []) LColor.r LColor.b
    cert72_seen_40_12_3 cert72_layer_40_12_3_eq 24

theorem cert72_step_40_12 :
    closedCollarIndexStepBool word fiber72 40 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_40_12)
    (by decide) (by decide)
    (by simpa [cert72_move_40_12] using cert72_component_40_12_eq)
    (by decide) (by decide) (by decide)

def cert72_move_40_44 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_40_44 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_40_44_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_40_44_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_40_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.b LColor.p cert72_seen_40_44_0 = cert72_layer_40_44_0 := by
  decide

def cert72_seen_40_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_40_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_40_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.b LColor.p cert72_seen_40_44_1 = cert72_layer_40_44_1 := by
  decide

def cert72_seen_40_44_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_40_44_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_40_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.b LColor.p cert72_seen_40_44_2 = cert72_layer_40_44_2 := by
  decide

def cert72_seen_40_44_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_40_44_3 : List ChainEdge :=
  []

theorem cert72_layer_40_44_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 40 [])
      LColor.b LColor.p cert72_seen_40_44_3 = cert72_layer_40_44_3 := by
  decide

theorem cert72_component_40_44_eq :
    closedCollarComponent word (listGetD fiber72 40 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_40_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 40 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.b LColor.p 27 cert72_seen_40_44_0 = cert72_component_40_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.b LColor.p
    cert72_seen_40_44_0 cert72_layer_40_44_0 26 cert72_layer_40_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.b LColor.p 26 cert72_seen_40_44_1 = cert72_component_40_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.b LColor.p
    cert72_seen_40_44_1 cert72_layer_40_44_1 25 cert72_layer_40_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.b LColor.p 25 cert72_seen_40_44_2 = cert72_component_40_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 40 []) LColor.b LColor.p
    cert72_seen_40_44_2 cert72_layer_40_44_2 24 cert72_layer_40_44_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 40 [])
      LColor.b LColor.p 24 cert72_seen_40_44_3 = cert72_component_40_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 40 []) LColor.b LColor.p
    cert72_seen_40_44_3 cert72_layer_40_44_3_eq 24

theorem cert72_step_40_44 :
    closedCollarIndexStepBool word fiber72 40 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_40_44)
    (by decide) (by decide)
    (by simpa [cert72_move_40_44] using cert72_component_40_44_eq)
    (by decide) (by decide) (by decide)

def cert72_move_41_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_41_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_41_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_41_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_41_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.r LColor.b cert72_seen_41_13_0 = cert72_layer_41_13_0 := by
  decide

def cert72_seen_41_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_41_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_41_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.r LColor.b cert72_seen_41_13_1 = cert72_layer_41_13_1 := by
  decide

def cert72_seen_41_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_41_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_41_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.r LColor.b cert72_seen_41_13_2 = cert72_layer_41_13_2 := by
  decide

def cert72_seen_41_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_41_13_3 : List ChainEdge :=
  []

theorem cert72_layer_41_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.r LColor.b cert72_seen_41_13_3 = cert72_layer_41_13_3 := by
  decide

theorem cert72_component_41_13_eq :
    closedCollarComponent word (listGetD fiber72 41 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_41_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 41 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.r LColor.b 27 cert72_seen_41_13_0 = cert72_component_41_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.r LColor.b
    cert72_seen_41_13_0 cert72_layer_41_13_0 26 cert72_layer_41_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.r LColor.b 26 cert72_seen_41_13_1 = cert72_component_41_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.r LColor.b
    cert72_seen_41_13_1 cert72_layer_41_13_1 25 cert72_layer_41_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.r LColor.b 25 cert72_seen_41_13_2 = cert72_component_41_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.r LColor.b
    cert72_seen_41_13_2 cert72_layer_41_13_2 24 cert72_layer_41_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.r LColor.b 24 cert72_seen_41_13_3 = cert72_component_41_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 41 []) LColor.r LColor.b
    cert72_seen_41_13_3 cert72_layer_41_13_3_eq 24

theorem cert72_step_41_13 :
    closedCollarIndexStepBool word fiber72 41 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_41_13)
    (by decide) (by decide)
    (by simpa [cert72_move_41_13] using cert72_component_41_13_eq)
    (by decide) (by decide) (by decide)

def cert72_move_41_45 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_41_45 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_41_45_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_41_45_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_41_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.b LColor.p cert72_seen_41_45_0 = cert72_layer_41_45_0 := by
  decide

def cert72_seen_41_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_41_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_41_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.b LColor.p cert72_seen_41_45_1 = cert72_layer_41_45_1 := by
  decide

def cert72_seen_41_45_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_41_45_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_41_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.b LColor.p cert72_seen_41_45_2 = cert72_layer_41_45_2 := by
  decide

def cert72_seen_41_45_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_41_45_3 : List ChainEdge :=
  []

theorem cert72_layer_41_45_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 41 [])
      LColor.b LColor.p cert72_seen_41_45_3 = cert72_layer_41_45_3 := by
  decide

theorem cert72_component_41_45_eq :
    closedCollarComponent word (listGetD fiber72 41 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_41_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 41 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.b LColor.p 27 cert72_seen_41_45_0 = cert72_component_41_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.b LColor.p
    cert72_seen_41_45_0 cert72_layer_41_45_0 26 cert72_layer_41_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.b LColor.p 26 cert72_seen_41_45_1 = cert72_component_41_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.b LColor.p
    cert72_seen_41_45_1 cert72_layer_41_45_1 25 cert72_layer_41_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.b LColor.p 25 cert72_seen_41_45_2 = cert72_component_41_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 41 []) LColor.b LColor.p
    cert72_seen_41_45_2 cert72_layer_41_45_2 24 cert72_layer_41_45_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 41 [])
      LColor.b LColor.p 24 cert72_seen_41_45_3 = cert72_component_41_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 41 []) LColor.b LColor.p
    cert72_seen_41_45_3 cert72_layer_41_45_3_eq 24

theorem cert72_step_41_45 :
    closedCollarIndexStepBool word fiber72 41 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_41_45)
    (by decide) (by decide)
    (by simpa [cert72_move_41_45] using cert72_component_41_45_eq)
    (by decide) (by decide) (by decide)

def cert72_move_42_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_42_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_42_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_42_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_42_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.r LColor.b cert72_seen_42_14_0 = cert72_layer_42_14_0 := by
  decide

def cert72_seen_42_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_42_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_42_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.r LColor.b cert72_seen_42_14_1 = cert72_layer_42_14_1 := by
  decide

def cert72_seen_42_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_42_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_42_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.r LColor.b cert72_seen_42_14_2 = cert72_layer_42_14_2 := by
  decide

def cert72_seen_42_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_42_14_3 : List ChainEdge :=
  []

theorem cert72_layer_42_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.r LColor.b cert72_seen_42_14_3 = cert72_layer_42_14_3 := by
  decide

theorem cert72_component_42_14_eq :
    closedCollarComponent word (listGetD fiber72 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_42_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.r LColor.b 27 cert72_seen_42_14_0 = cert72_component_42_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.r LColor.b
    cert72_seen_42_14_0 cert72_layer_42_14_0 26 cert72_layer_42_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.r LColor.b 26 cert72_seen_42_14_1 = cert72_component_42_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.r LColor.b
    cert72_seen_42_14_1 cert72_layer_42_14_1 25 cert72_layer_42_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.r LColor.b 25 cert72_seen_42_14_2 = cert72_component_42_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.r LColor.b
    cert72_seen_42_14_2 cert72_layer_42_14_2 24 cert72_layer_42_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.r LColor.b 24 cert72_seen_42_14_3 = cert72_component_42_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 42 []) LColor.r LColor.b
    cert72_seen_42_14_3 cert72_layer_42_14_3_eq 24

theorem cert72_step_42_14 :
    closedCollarIndexStepBool word fiber72 42 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_42_14)
    (by decide) (by decide)
    (by simpa [cert72_move_42_14] using cert72_component_42_14_eq)
    (by decide) (by decide) (by decide)

def cert72_move_42_46 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_42_46 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_42_46_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_42_46_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_42_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.b LColor.p cert72_seen_42_46_0 = cert72_layer_42_46_0 := by
  decide

def cert72_seen_42_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_42_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_42_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.b LColor.p cert72_seen_42_46_1 = cert72_layer_42_46_1 := by
  decide

def cert72_seen_42_46_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_42_46_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_42_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.b LColor.p cert72_seen_42_46_2 = cert72_layer_42_46_2 := by
  decide

def cert72_seen_42_46_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_42_46_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_42_46_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.b LColor.p cert72_seen_42_46_3 = cert72_layer_42_46_3 := by
  decide

def cert72_seen_42_46_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_42_46_4 : List ChainEdge :=
  []

theorem cert72_layer_42_46_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 42 [])
      LColor.b LColor.p cert72_seen_42_46_4 = cert72_layer_42_46_4 := by
  decide

theorem cert72_component_42_46_eq :
    closedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_42_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 42 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p 27 cert72_seen_42_46_0 = cert72_component_42_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.b LColor.p
    cert72_seen_42_46_0 cert72_layer_42_46_0 26 cert72_layer_42_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p 26 cert72_seen_42_46_1 = cert72_component_42_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.b LColor.p
    cert72_seen_42_46_1 cert72_layer_42_46_1 25 cert72_layer_42_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p 25 cert72_seen_42_46_2 = cert72_component_42_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.b LColor.p
    cert72_seen_42_46_2 cert72_layer_42_46_2 24 cert72_layer_42_46_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p 24 cert72_seen_42_46_3 = cert72_component_42_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 42 []) LColor.b LColor.p
    cert72_seen_42_46_3 cert72_layer_42_46_3 23 cert72_layer_42_46_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 42 [])
      LColor.b LColor.p 23 cert72_seen_42_46_4 = cert72_component_42_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 42 []) LColor.b LColor.p
    cert72_seen_42_46_4 cert72_layer_42_46_4_eq 23

theorem cert72_step_42_46 :
    closedCollarIndexStepBool word fiber72 42 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_42_46)
    (by decide) (by decide)
    (by simpa [cert72_move_42_46] using cert72_component_42_46_eq)
    (by decide) (by decide) (by decide)

def cert72_move_43_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert72_component_43_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_seen_43_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert72_layer_43_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert72_layer_43_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 43 [])
      LColor.r LColor.b cert72_seen_43_15_0 = cert72_layer_43_15_0 := by
  decide

def cert72_seen_43_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert72_layer_43_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert72_layer_43_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 43 [])
      LColor.r LColor.b cert72_seen_43_15_1 = cert72_layer_43_15_1 := by
  decide

def cert72_seen_43_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_43_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert72_layer_43_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 43 [])
      LColor.r LColor.b cert72_seen_43_15_2 = cert72_layer_43_15_2 := by
  decide

def cert72_seen_43_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert72_layer_43_15_3 : List ChainEdge :=
  []

theorem cert72_layer_43_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 43 [])
      LColor.r LColor.b cert72_seen_43_15_3 = cert72_layer_43_15_3 := by
  decide

theorem cert72_component_43_15_eq :
    closedCollarComponent word (listGetD fiber72 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert72_component_43_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 43 [])
      LColor.r LColor.b 27 cert72_seen_43_15_0 = cert72_component_43_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 43 []) LColor.r LColor.b
    cert72_seen_43_15_0 cert72_layer_43_15_0 26 cert72_layer_43_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 43 [])
      LColor.r LColor.b 26 cert72_seen_43_15_1 = cert72_component_43_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 43 []) LColor.r LColor.b
    cert72_seen_43_15_1 cert72_layer_43_15_1 25 cert72_layer_43_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 43 [])
      LColor.r LColor.b 25 cert72_seen_43_15_2 = cert72_component_43_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 43 []) LColor.r LColor.b
    cert72_seen_43_15_2 cert72_layer_43_15_2 24 cert72_layer_43_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 43 [])
      LColor.r LColor.b 24 cert72_seen_43_15_3 = cert72_component_43_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 43 []) LColor.r LColor.b
    cert72_seen_43_15_3 cert72_layer_43_15_3_eq 24

theorem cert72_step_43_15 :
    closedCollarIndexStepBool word fiber72 43 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_43_15)
    (by decide) (by decide)
    (by simpa [cert72_move_43_15] using cert72_component_43_15_eq)
    (by decide) (by decide) (by decide)

def cert72_move_44_40 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_44_40 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_44_40_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_44_40_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_44_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.b LColor.p cert72_seen_44_40_0 = cert72_layer_44_40_0 := by
  decide

def cert72_seen_44_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_44_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_44_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.b LColor.p cert72_seen_44_40_1 = cert72_layer_44_40_1 := by
  decide

def cert72_seen_44_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_44_40_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_44_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.b LColor.p cert72_seen_44_40_2 = cert72_layer_44_40_2 := by
  decide

def cert72_seen_44_40_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_44_40_3 : List ChainEdge :=
  []

theorem cert72_layer_44_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.b LColor.p cert72_seen_44_40_3 = cert72_layer_44_40_3 := by
  decide

theorem cert72_component_44_40_eq :
    closedCollarComponent word (listGetD fiber72 44 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_44_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 44 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.b LColor.p 27 cert72_seen_44_40_0 = cert72_component_44_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 44 []) LColor.b LColor.p
    cert72_seen_44_40_0 cert72_layer_44_40_0 26 cert72_layer_44_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.b LColor.p 26 cert72_seen_44_40_1 = cert72_component_44_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 44 []) LColor.b LColor.p
    cert72_seen_44_40_1 cert72_layer_44_40_1 25 cert72_layer_44_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.b LColor.p 25 cert72_seen_44_40_2 = cert72_component_44_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 44 []) LColor.b LColor.p
    cert72_seen_44_40_2 cert72_layer_44_40_2 24 cert72_layer_44_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.b LColor.p 24 cert72_seen_44_40_3 = cert72_component_44_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 44 []) LColor.b LColor.p
    cert72_seen_44_40_3 cert72_layer_44_40_3_eq 24

theorem cert72_step_44_40 :
    closedCollarIndexStepBool word fiber72 44 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_44_40)
    (by decide) (by decide)
    (by simpa [cert72_move_44_40] using cert72_component_44_40_eq)
    (by decide) (by decide) (by decide)

def cert72_move_44_47 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_44_47 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_44_47_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_44_47_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_44_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.r LColor.p cert72_seen_44_47_0 = cert72_layer_44_47_0 := by
  decide

def cert72_seen_44_47_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_44_47_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_44_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.r LColor.p cert72_seen_44_47_1 = cert72_layer_44_47_1 := by
  decide

def cert72_seen_44_47_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_44_47_2 : List ChainEdge :=
  []

theorem cert72_layer_44_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 44 [])
      LColor.r LColor.p cert72_seen_44_47_2 = cert72_layer_44_47_2 := by
  decide

theorem cert72_component_44_47_eq :
    closedCollarComponent word (listGetD fiber72 44 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_44_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 44 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.r LColor.p 27 cert72_seen_44_47_0 = cert72_component_44_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 44 []) LColor.r LColor.p
    cert72_seen_44_47_0 cert72_layer_44_47_0 26 cert72_layer_44_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.r LColor.p 26 cert72_seen_44_47_1 = cert72_component_44_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 44 []) LColor.r LColor.p
    cert72_seen_44_47_1 cert72_layer_44_47_1 25 cert72_layer_44_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 44 [])
      LColor.r LColor.p 25 cert72_seen_44_47_2 = cert72_component_44_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 44 []) LColor.r LColor.p
    cert72_seen_44_47_2 cert72_layer_44_47_2_eq 25

theorem cert72_step_44_47 :
    closedCollarIndexStepBool word fiber72 44 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_44_47)
    (by decide) (by decide)
    (by simpa [cert72_move_44_47] using cert72_component_44_47_eq)
    (by decide) (by decide) (by decide)

def cert72_move_45_41 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_45_41 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_seen_45_41_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_45_41_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_45_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 45 [])
      LColor.b LColor.p cert72_seen_45_41_0 = cert72_layer_45_41_0 := by
  decide

def cert72_seen_45_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_45_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_45_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 45 [])
      LColor.b LColor.p cert72_seen_45_41_1 = cert72_layer_45_41_1 := by
  decide

def cert72_seen_45_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_45_41_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_45_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 45 [])
      LColor.b LColor.p cert72_seen_45_41_2 = cert72_layer_45_41_2 := by
  decide

def cert72_seen_45_41_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_45_41_3 : List ChainEdge :=
  []

theorem cert72_layer_45_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 45 [])
      LColor.b LColor.p cert72_seen_45_41_3 = cert72_layer_45_41_3 := by
  decide

theorem cert72_component_45_41_eq :
    closedCollarComponent word (listGetD fiber72 45 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_45_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 45 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 45 [])
      LColor.b LColor.p 27 cert72_seen_45_41_0 = cert72_component_45_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 45 []) LColor.b LColor.p
    cert72_seen_45_41_0 cert72_layer_45_41_0 26 cert72_layer_45_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 45 [])
      LColor.b LColor.p 26 cert72_seen_45_41_1 = cert72_component_45_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 45 []) LColor.b LColor.p
    cert72_seen_45_41_1 cert72_layer_45_41_1 25 cert72_layer_45_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 45 [])
      LColor.b LColor.p 25 cert72_seen_45_41_2 = cert72_component_45_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 45 []) LColor.b LColor.p
    cert72_seen_45_41_2 cert72_layer_45_41_2 24 cert72_layer_45_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 45 [])
      LColor.b LColor.p 24 cert72_seen_45_41_3 = cert72_component_45_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 45 []) LColor.b LColor.p
    cert72_seen_45_41_3 cert72_layer_45_41_3_eq 24

theorem cert72_step_45_41 :
    closedCollarIndexStepBool word fiber72 45 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_45_41)
    (by decide) (by decide)
    (by simpa [cert72_move_45_41] using cert72_component_45_41_eq)
    (by decide) (by decide) (by decide)

def cert72_move_46_42 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert72_component_46_42 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_46_42_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert72_layer_46_42_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert72_layer_46_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 46 [])
      LColor.b LColor.p cert72_seen_46_42_0 = cert72_layer_46_42_0 := by
  decide

def cert72_seen_46_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert72_layer_46_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert72_layer_46_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 46 [])
      LColor.b LColor.p cert72_seen_46_42_1 = cert72_layer_46_42_1 := by
  decide

def cert72_seen_46_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert72_layer_46_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert72_layer_46_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 46 [])
      LColor.b LColor.p cert72_seen_46_42_2 = cert72_layer_46_42_2 := by
  decide

def cert72_seen_46_42_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert72_layer_46_42_3 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_46_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber72 46 [])
      LColor.b LColor.p cert72_seen_46_42_3 = cert72_layer_46_42_3 := by
  decide

def cert72_seen_46_42_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_46_42_4 : List ChainEdge :=
  []

theorem cert72_layer_46_42_4_eq :
    closedCollarComponentLayer word (listGetD fiber72 46 [])
      LColor.b LColor.p cert72_seen_46_42_4 = cert72_layer_46_42_4 := by
  decide

theorem cert72_component_46_42_eq :
    closedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert72_component_46_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 46 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p 27 cert72_seen_46_42_0 = cert72_component_46_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 46 []) LColor.b LColor.p
    cert72_seen_46_42_0 cert72_layer_46_42_0 26 cert72_layer_46_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p 26 cert72_seen_46_42_1 = cert72_component_46_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 46 []) LColor.b LColor.p
    cert72_seen_46_42_1 cert72_layer_46_42_1 25 cert72_layer_46_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p 25 cert72_seen_46_42_2 = cert72_component_46_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 46 []) LColor.b LColor.p
    cert72_seen_46_42_2 cert72_layer_46_42_2 24 cert72_layer_46_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p 24 cert72_seen_46_42_3 = cert72_component_46_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 46 []) LColor.b LColor.p
    cert72_seen_46_42_3 cert72_layer_46_42_3 23 cert72_layer_46_42_3_eq]
  change closeClosedCollarComponent word (listGetD fiber72 46 [])
      LColor.b LColor.p 23 cert72_seen_46_42_4 = cert72_component_46_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 46 []) LColor.b LColor.p
    cert72_seen_46_42_4 cert72_layer_46_42_4_eq 23

theorem cert72_step_46_42 :
    closedCollarIndexStepBool word fiber72 46 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_46_42)
    (by decide) (by decide)
    (by simpa [cert72_move_46_42] using cert72_component_46_42_eq)
    (by decide) (by decide) (by decide)

def cert72_move_47_44 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert72_component_47_44 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_seen_47_44_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert72_layer_47_44_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert72_layer_47_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber72 47 [])
      LColor.r LColor.p cert72_seen_47_44_0 = cert72_layer_47_44_0 := by
  decide

def cert72_seen_47_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert72_layer_47_44_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }]

theorem cert72_layer_47_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber72 47 [])
      LColor.r LColor.p cert72_seen_47_44_1 = cert72_layer_47_44_1 := by
  decide

def cert72_seen_47_44_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert72_layer_47_44_2 : List ChainEdge :=
  []

theorem cert72_layer_47_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber72 47 [])
      LColor.r LColor.p cert72_seen_47_44_2 = cert72_layer_47_44_2 := by
  decide

theorem cert72_component_47_44_eq :
    closedCollarComponent word (listGetD fiber72 47 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert72_component_47_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber72 47 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber72 47 [])
      LColor.r LColor.p 27 cert72_seen_47_44_0 = cert72_component_47_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 47 []) LColor.r LColor.p
    cert72_seen_47_44_0 cert72_layer_47_44_0 26 cert72_layer_47_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber72 47 [])
      LColor.r LColor.p 26 cert72_seen_47_44_1 = cert72_component_47_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber72 47 []) LColor.r LColor.p
    cert72_seen_47_44_1 cert72_layer_47_44_1 25 cert72_layer_47_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber72 47 [])
      LColor.r LColor.p 25 cert72_seen_47_44_2 = cert72_component_47_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber72 47 []) LColor.r LColor.p
    cert72_seen_47_44_2 cert72_layer_47_44_2_eq 25

theorem cert72_step_47_44 :
    closedCollarIndexStepBool word fiber72 47 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert72_move_47_44)
    (by decide) (by decide)
    (by simpa [cert72_move_47_44] using cert72_component_47_44_eq)
    (by decide) (by decide) (by decide)

theorem cert72_row_0 :
    closedCollarParentIndexValid word fiber72 cert72.parents 0 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length]

theorem cert72_row_1 :
    closedCollarParentIndexValid word fiber72 cert72.parents 1 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_1_0, cert72_step_0_1]

theorem cert72_row_2 :
    closedCollarParentIndexValid word fiber72 cert72.parents 2 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_2_0, cert72_step_0_2]

theorem cert72_row_3 :
    closedCollarParentIndexValid word fiber72 cert72.parents 3 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_3_1, cert72_step_1_3]

theorem cert72_row_4 :
    closedCollarParentIndexValid word fiber72 cert72.parents 4 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_4_0, cert72_step_0_4]

theorem cert72_row_5 :
    closedCollarParentIndexValid word fiber72 cert72.parents 5 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_5_1, cert72_step_1_5]

theorem cert72_row_6 :
    closedCollarParentIndexValid word fiber72 cert72.parents 6 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_6_2, cert72_step_2_6]

theorem cert72_row_7 :
    closedCollarParentIndexValid word fiber72 cert72.parents 7 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_7_3, cert72_step_3_7]

theorem cert72_row_8 :
    closedCollarParentIndexValid word fiber72 cert72.parents 8 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_8_4, cert72_step_4_8]

theorem cert72_row_9 :
    closedCollarParentIndexValid word fiber72 cert72.parents 9 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_9_5, cert72_step_5_9]

theorem cert72_row_10 :
    closedCollarParentIndexValid word fiber72 cert72.parents 10 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_10_6, cert72_step_6_10]

theorem cert72_row_11 :
    closedCollarParentIndexValid word fiber72 cert72.parents 11 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_11_7, cert72_step_7_11]

theorem cert72_row_12 :
    closedCollarParentIndexValid word fiber72 cert72.parents 12 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_12_0, cert72_step_0_12]

theorem cert72_row_13 :
    closedCollarParentIndexValid word fiber72 cert72.parents 13 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_13_1, cert72_step_1_13]

theorem cert72_row_14 :
    closedCollarParentIndexValid word fiber72 cert72.parents 14 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_14_2, cert72_step_2_14]

theorem cert72_row_15 :
    closedCollarParentIndexValid word fiber72 cert72.parents 15 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_15_3, cert72_step_3_15]

theorem cert72_row_16 :
    closedCollarParentIndexValid word fiber72 cert72.parents 16 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_16_0, cert72_step_0_16]

theorem cert72_row_17 :
    closedCollarParentIndexValid word fiber72 cert72.parents 17 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_17_1, cert72_step_1_17]

theorem cert72_row_18 :
    closedCollarParentIndexValid word fiber72 cert72.parents 18 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_18_2, cert72_step_2_18]

theorem cert72_row_19 :
    closedCollarParentIndexValid word fiber72 cert72.parents 19 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_19_3, cert72_step_3_19]

theorem cert72_row_20 :
    closedCollarParentIndexValid word fiber72 cert72.parents 20 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_20_16, cert72_step_16_20]

theorem cert72_row_21 :
    closedCollarParentIndexValid word fiber72 cert72.parents 21 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_21_17, cert72_step_17_21]

theorem cert72_row_22 :
    closedCollarParentIndexValid word fiber72 cert72.parents 22 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_22_18, cert72_step_18_22]

theorem cert72_row_23 :
    closedCollarParentIndexValid word fiber72 cert72.parents 23 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_23_20, cert72_step_20_23]

theorem cert72_row_24 :
    closedCollarParentIndexValid word fiber72 cert72.parents 24 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_24_4, cert72_step_4_24]

theorem cert72_row_25 :
    closedCollarParentIndexValid word fiber72 cert72.parents 25 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_25_5, cert72_step_5_25]

theorem cert72_row_26 :
    closedCollarParentIndexValid word fiber72 cert72.parents 26 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_26_6, cert72_step_6_26]

theorem cert72_row_27 :
    closedCollarParentIndexValid word fiber72 cert72.parents 27 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_27_7, cert72_step_7_27]

theorem cert72_row_28 :
    closedCollarParentIndexValid word fiber72 cert72.parents 28 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_28_24, cert72_step_24_28]

theorem cert72_row_29 :
    closedCollarParentIndexValid word fiber72 cert72.parents 29 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_29_25, cert72_step_25_29]

theorem cert72_row_30 :
    closedCollarParentIndexValid word fiber72 cert72.parents 30 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_30_26, cert72_step_26_30]

theorem cert72_row_31 :
    closedCollarParentIndexValid word fiber72 cert72.parents 31 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_31_28, cert72_step_28_31]

theorem cert72_row_32 :
    closedCollarParentIndexValid word fiber72 cert72.parents 32 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_32_16, cert72_step_16_32]

theorem cert72_row_33 :
    closedCollarParentIndexValid word fiber72 cert72.parents 33 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_33_17, cert72_step_17_33]

theorem cert72_row_34 :
    closedCollarParentIndexValid word fiber72 cert72.parents 34 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_34_18, cert72_step_18_34]

theorem cert72_row_35 :
    closedCollarParentIndexValid word fiber72 cert72.parents 35 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_35_19, cert72_step_19_35]

theorem cert72_row_36 :
    closedCollarParentIndexValid word fiber72 cert72.parents 36 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_36_20, cert72_step_20_36]

theorem cert72_row_37 :
    closedCollarParentIndexValid word fiber72 cert72.parents 37 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_37_21, cert72_step_21_37]

theorem cert72_row_38 :
    closedCollarParentIndexValid word fiber72 cert72.parents 38 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_38_22, cert72_step_22_38]

theorem cert72_row_39 :
    closedCollarParentIndexValid word fiber72 cert72.parents 39 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_39_23, cert72_step_23_39]

theorem cert72_row_40 :
    closedCollarParentIndexValid word fiber72 cert72.parents 40 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_40_12, cert72_step_12_40]

theorem cert72_row_41 :
    closedCollarParentIndexValid word fiber72 cert72.parents 41 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_41_13, cert72_step_13_41]

theorem cert72_row_42 :
    closedCollarParentIndexValid word fiber72 cert72.parents 42 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_42_14, cert72_step_14_42]

theorem cert72_row_43 :
    closedCollarParentIndexValid word fiber72 cert72.parents 43 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_43_15, cert72_step_15_43]

theorem cert72_row_44 :
    closedCollarParentIndexValid word fiber72 cert72.parents 44 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_44_40, cert72_step_40_44]

theorem cert72_row_45 :
    closedCollarParentIndexValid word fiber72 cert72.parents 45 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_45_41, cert72_step_41_45]

theorem cert72_row_46 :
    closedCollarParentIndexValid word fiber72 cert72.parents 46 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_46_42, cert72_step_42_46]

theorem cert72_row_47 :
    closedCollarParentIndexValid word fiber72 cert72.parents 47 = true := by
  have cert72_fiber_length : fiber72.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert72, listGetD, cert72_fiber_length, cert72_step_47_44, cert72_step_44_47]

theorem cert72_rows :
    closedCollarSpineRowsValid word fiber72 cert72.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert72_fiber_length : fiber72.length = 48 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert72_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert72_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert72_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert72_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert72_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert72_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert72_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert72_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert72_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert72_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert72_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert72_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert72_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert72_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert72_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert72_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert72_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert72_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert72_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert72_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert72_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert72_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert72_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert72_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert72_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert72_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert72_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert72_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert72_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert72_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert72_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert72_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert72_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert72_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert72_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert72_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert72_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert72_row_43
  by_cases h44 : idx = 44
  · subst idx
    exact cert72_row_44
  by_cases h45 : idx = 45
  · subst idx
    exact cert72_row_45
  by_cases h46 : idx = 46
  · subst idx
    exact cert72_row_46
  by_cases h47 : idx = 47
  · subst idx
    exact cert72_row_47
  · omega

theorem cert72_root :
    closedCollarSpineParentsReachRoot fiber72 cert72 = true := by
  decide

theorem cert72_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.r] := by
  change closedCollarFiberKempeConnected word cert72.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert72 fiber72_eq cert72_rows cert72_root


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
