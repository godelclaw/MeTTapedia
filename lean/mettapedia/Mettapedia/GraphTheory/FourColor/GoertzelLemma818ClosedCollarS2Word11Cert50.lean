import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word11

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast50 : List TauState :=
  [stateAt 0, stateAt 8, stateAt 16, stateAt 24, stateAt 64, stateAt 72, stateAt 80, stateAt 88]

theorem keyedLast50_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.b, LColor.p]) =
      keyedLast50 := by
  decide

def fiber50OuterChunks : List (List (List TauState)) :=
[
  []
, []
, []
, []
, []
, [
  [stateAt 80, stateAt 80, stateAt 80]
, [stateAt 80, stateAt 81, stateAt 88]
, [stateAt 80, stateAt 82, stateAt 16]
, [stateAt 80, stateAt 83, stateAt 24]
, [stateAt 80, stateAt 102, stateAt 64]
, [stateAt 80, stateAt 103, stateAt 72]
, [stateAt 81, stateAt 88, stateAt 80]
, [stateAt 81, stateAt 89, stateAt 88]
, [stateAt 81, stateAt 90, stateAt 16]
, [stateAt 81, stateAt 91, stateAt 24]
, [stateAt 81, stateAt 110, stateAt 64]
, [stateAt 81, stateAt 111, stateAt 72]
, [stateAt 82, stateAt 16, stateAt 80]
, [stateAt 82, stateAt 17, stateAt 88]
, [stateAt 82, stateAt 18, stateAt 16]
, [stateAt 82, stateAt 19, stateAt 24]
, [stateAt 82, stateAt 34, stateAt 0]
, [stateAt 82, stateAt 35, stateAt 8]
, [stateAt 83, stateAt 24, stateAt 80]
, [stateAt 83, stateAt 25, stateAt 88]
, [stateAt 83, stateAt 26, stateAt 16]
, [stateAt 83, stateAt 27, stateAt 24]
, [stateAt 83, stateAt 42, stateAt 0]
, [stateAt 83, stateAt 43, stateAt 8]
]
, [
  [stateAt 100, stateAt 134, stateAt 0]
, [stateAt 100, stateAt 135, stateAt 8]
, [stateAt 100, stateAt 182, stateAt 64]
, [stateAt 100, stateAt 183, stateAt 72]
, [stateAt 101, stateAt 142, stateAt 0]
, [stateAt 101, stateAt 143, stateAt 8]
, [stateAt 101, stateAt 190, stateAt 64]
, [stateAt 101, stateAt 191, stateAt 72]
, [stateAt 102, stateAt 64, stateAt 80]
, [stateAt 102, stateAt 65, stateAt 88]
, [stateAt 102, stateAt 66, stateAt 16]
, [stateAt 102, stateAt 67, stateAt 24]
, [stateAt 102, stateAt 118, stateAt 64]
, [stateAt 102, stateAt 119, stateAt 72]
, [stateAt 103, stateAt 72, stateAt 80]
, [stateAt 103, stateAt 73, stateAt 88]
, [stateAt 103, stateAt 74, stateAt 16]
, [stateAt 103, stateAt 75, stateAt 24]
, [stateAt 103, stateAt 126, stateAt 64]
, [stateAt 103, stateAt 127, stateAt 72]
]
, []
, []
, []
, []
, []
]

def fiber50 : List (List TauState) :=
  fiber50OuterChunks.flatten

theorem fiber50_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 0 []) =
      listGetD fiber50OuterChunks 0 [] := by
  decide

theorem fiber50_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 1 []) =
      listGetD fiber50OuterChunks 1 [] := by
  decide

theorem fiber50_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 2 []) =
      listGetD fiber50OuterChunks 2 [] := by
  decide

theorem fiber50_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 3 []) =
      listGetD fiber50OuterChunks 3 [] := by
  decide

theorem fiber50_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 4 []) =
      listGetD fiber50OuterChunks 4 [] := by
  decide

theorem fiber50_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 5 []) =
      listGetD fiber50OuterChunks 5 [] := by
  decide

theorem fiber50_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 6 []) =
      listGetD fiber50OuterChunks 6 [] := by
  decide

theorem fiber50_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 7 []) =
      listGetD fiber50OuterChunks 7 [] := by
  decide

theorem fiber50_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 8 []) =
      listGetD fiber50OuterChunks 8 [] := by
  decide

theorem fiber50_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 9 []) =
      listGetD fiber50OuterChunks 9 [] := by
  decide

theorem fiber50_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 10 []) =
      listGetD fiber50OuterChunks 10 [] := by
  decide

theorem fiber50_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks 11 []) =
      listGetD fiber50OuterChunks 11 [] := by
  decide

theorem fiber50_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast50
        (listGetD tauStateChunks idx []) =
      listGetD fiber50OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber50_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber50_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber50_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber50_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber50_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber50_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber50_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber50_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber50_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber50_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber50_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber50_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber50_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast50 =
      fiber50 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast50 tauStateChunks fiber50OuterChunks
    tauStateChunks_eq (by rfl) fiber50_outer_get
  simpa [fiber50] using h

theorem fiber50_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.b, LColor.p] = fiber50 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.b, LColor.p] keyedLast50_eq
  exact hfrom.trans fiber50_keyedFrom_eq

theorem fiber50_eq :
    closedCollarFiber word [LColor.b, LColor.p, LColor.b, LColor.p] = fiber50 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.mirror [LColor.b, LColor.p, LColor.b, LColor.p]
  exact hfast.trans fiber50_keyed_eq

def cert50 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.p, LColor.b, LColor.p],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 0, 1, 1, 0, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 13, 12, 40, 41, 42, 43, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5] }

def cert50_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert50_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert50_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_1_0 = cert50_layer_0_1_0 := by
  decide

def cert50_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_0_1_1 : List ChainEdge :=
  []

theorem cert50_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_1_1 = cert50_layer_0_1_1 := by
  decide

theorem cert50_component_0_1_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert50_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 27 cert50_seen_0_1_0 = cert50_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_1_0 cert50_layer_0_1_0 26 cert50_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 26 cert50_seen_0_1_1 = cert50_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_1_1 cert50_layer_0_1_1_eq 26

theorem cert50_step_0_1 :
    closedCollarIndexStepBool word fiber50 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_1)
    (by decide) (by decide)
    (by simpa [cert50_move_0_1] using cert50_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert50_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_0 = cert50_layer_0_2_0 := by
  decide

def cert50_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_0_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_1 = cert50_layer_0_2_1 := by
  decide

def cert50_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_0_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_2 = cert50_layer_0_2_2 := by
  decide

def cert50_seen_0_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_0_2_3 : List ChainEdge :=
  []

theorem cert50_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_2_3 = cert50_layer_0_2_3 := by
  decide

theorem cert50_component_0_2_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert50_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 27 cert50_seen_0_2_0 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_0 cert50_layer_0_2_0 26 cert50_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 26 cert50_seen_0_2_1 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_1 cert50_layer_0_2_1 25 cert50_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 25 cert50_seen_0_2_2 = cert50_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_2 cert50_layer_0_2_2 24 cert50_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 24 cert50_seen_0_2_3 = cert50_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_2_3 cert50_layer_0_2_3_eq 24

theorem cert50_step_0_2 :
    closedCollarIndexStepBool word fiber50 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_2)
    (by decide) (by decide)
    (by simpa [cert50_move_0_2] using cert50_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert50_component_0_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_seen_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_0 = cert50_layer_0_5_0 := by
  decide

def cert50_seen_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_1 = cert50_layer_0_5_1 := by
  decide

def cert50_seen_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_2 = cert50_layer_0_5_2 := by
  decide

def cert50_seen_0_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_0_5_3 : List ChainEdge :=
  []

theorem cert50_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_5_3 = cert50_layer_0_5_3 := by
  decide

theorem cert50_component_0_5_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert50_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 27 cert50_seen_0_5_0 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_0 cert50_layer_0_5_0 26 cert50_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 26 cert50_seen_0_5_1 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_1 cert50_layer_0_5_1 25 cert50_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 25 cert50_seen_0_5_2 = cert50_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_2 cert50_layer_0_5_2 24 cert50_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 24 cert50_seen_0_5_3 = cert50_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_5_3 cert50_layer_0_5_3_eq 24

theorem cert50_step_0_5 :
    closedCollarIndexStepBool word fiber50 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_5)
    (by decide) (by decide)
    (by simpa [cert50_move_0_5] using cert50_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_6_0 = cert50_layer_0_6_0 := by
  decide

def cert50_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_0_6_1 : List ChainEdge :=
  []

theorem cert50_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.b LColor.p cert50_seen_0_6_1 = cert50_layer_0_6_1 := by
  decide

theorem cert50_component_0_6_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 27 cert50_seen_0_6_0 = cert50_component_0_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_6_0 cert50_layer_0_6_0 26 cert50_layer_0_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.b LColor.p 26 cert50_seen_0_6_1 = cert50_component_0_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.b LColor.p
    cert50_seen_0_6_1 cert50_layer_0_6_1_eq 26

theorem cert50_step_0_6 :
    closedCollarIndexStepBool word fiber50 0 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_6)
    (by decide) (by decide)
    (by simpa [cert50_move_0_6] using cert50_component_0_6_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_0_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_0_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_12_0 = cert50_layer_0_12_0 := by
  decide

def cert50_seen_0_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_0_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_0_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_12_1 = cert50_layer_0_12_1 := by
  decide

def cert50_seen_0_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_0_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_0_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_12_2 = cert50_layer_0_12_2 := by
  decide

def cert50_seen_0_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_0_12_3 : List ChainEdge :=
  []

theorem cert50_layer_0_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.b cert50_seen_0_12_3 = cert50_layer_0_12_3 := by
  decide

theorem cert50_component_0_12_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_0_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 27 cert50_seen_0_12_0 = cert50_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_12_0 cert50_layer_0_12_0 26 cert50_layer_0_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 26 cert50_seen_0_12_1 = cert50_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_12_1 cert50_layer_0_12_1 25 cert50_layer_0_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 25 cert50_seen_0_12_2 = cert50_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_12_2 cert50_layer_0_12_2 24 cert50_layer_0_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.b 24 cert50_seen_0_12_3 = cert50_component_0_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.b
    cert50_seen_0_12_3 cert50_layer_0_12_3_eq 24

theorem cert50_step_0_12 :
    closedCollarIndexStepBool word fiber50 0 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_12)
    (by decide) (by decide)
    (by simpa [cert50_move_0_12] using cert50_component_0_12_eq)
    (by decide) (by decide) (by decide)

def cert50_move_0_38 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_0_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_0_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_0_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_0_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_38_0 = cert50_layer_0_38_0 := by
  decide

def cert50_seen_0_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_0_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_0_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_38_1 = cert50_layer_0_38_1 := by
  decide

def cert50_seen_0_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_0_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_0_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_38_2 = cert50_layer_0_38_2 := by
  decide

def cert50_seen_0_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_0_38_3 : List ChainEdge :=
  []

theorem cert50_layer_0_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 0 [])
      LColor.r LColor.p cert50_seen_0_38_3 = cert50_layer_0_38_3 := by
  decide

theorem cert50_component_0_38_eq :
    closedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_0_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 27 cert50_seen_0_38_0 = cert50_component_0_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_38_0 cert50_layer_0_38_0 26 cert50_layer_0_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 26 cert50_seen_0_38_1 = cert50_component_0_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_38_1 cert50_layer_0_38_1 25 cert50_layer_0_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 25 cert50_seen_0_38_2 = cert50_component_0_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_38_2 cert50_layer_0_38_2 24 cert50_layer_0_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 0 [])
      LColor.r LColor.p 24 cert50_seen_0_38_3 = cert50_component_0_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 0 []) LColor.r LColor.p
    cert50_seen_0_38_3 cert50_layer_0_38_3_eq 24

theorem cert50_step_0_38 :
    closedCollarIndexStepBool word fiber50 0 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_0_38)
    (by decide) (by decide)
    (by simpa [cert50_move_0_38] using cert50_component_0_38_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert50_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert50_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_0_0 = cert50_layer_1_0_0 := by
  decide

def cert50_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_1_0_1 : List ChainEdge :=
  []

theorem cert50_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_0_1 = cert50_layer_1_0_1 := by
  decide

theorem cert50_component_1_0_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert50_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 27 cert50_seen_1_0_0 = cert50_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_0_0 cert50_layer_1_0_0 26 cert50_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 26 cert50_seen_1_0_1 = cert50_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_0_1 cert50_layer_1_0_1_eq 26

theorem cert50_step_1_0 :
    closedCollarIndexStepBool word fiber50 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_0)
    (by decide) (by decide)
    (by simpa [cert50_move_1_0] using cert50_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert50_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_0 = cert50_layer_1_3_0 := by
  decide

def cert50_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_1_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_1 = cert50_layer_1_3_1 := by
  decide

def cert50_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_1_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_2 = cert50_layer_1_3_2 := by
  decide

def cert50_seen_1_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_1_3_3 : List ChainEdge :=
  []

theorem cert50_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_3_3 = cert50_layer_1_3_3 := by
  decide

theorem cert50_component_1_3_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert50_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 27 cert50_seen_1_3_0 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_0 cert50_layer_1_3_0 26 cert50_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 26 cert50_seen_1_3_1 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_1 cert50_layer_1_3_1 25 cert50_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 25 cert50_seen_1_3_2 = cert50_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_2 cert50_layer_1_3_2 24 cert50_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 24 cert50_seen_1_3_3 = cert50_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_3_3 cert50_layer_1_3_3_eq 24

theorem cert50_step_1_3 :
    closedCollarIndexStepBool word fiber50 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_3)
    (by decide) (by decide)
    (by simpa [cert50_move_1_3] using cert50_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert50_component_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_0 = cert50_layer_1_4_0 := by
  decide

def cert50_seen_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_1 = cert50_layer_1_4_1 := by
  decide

def cert50_seen_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_2 = cert50_layer_1_4_2 := by
  decide

def cert50_seen_1_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_1_4_3 : List ChainEdge :=
  []

theorem cert50_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_4_3 = cert50_layer_1_4_3 := by
  decide

theorem cert50_component_1_4_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert50_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 27 cert50_seen_1_4_0 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_0 cert50_layer_1_4_0 26 cert50_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 26 cert50_seen_1_4_1 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_1 cert50_layer_1_4_1 25 cert50_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 25 cert50_seen_1_4_2 = cert50_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_2 cert50_layer_1_4_2 24 cert50_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 24 cert50_seen_1_4_3 = cert50_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_4_3 cert50_layer_1_4_3_eq 24

theorem cert50_step_1_4 :
    closedCollarIndexStepBool word fiber50 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_4)
    (by decide) (by decide)
    (by simpa [cert50_move_1_4] using cert50_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_7_0 = cert50_layer_1_7_0 := by
  decide

def cert50_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_1_7_1 : List ChainEdge :=
  []

theorem cert50_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.b LColor.p cert50_seen_1_7_1 = cert50_layer_1_7_1 := by
  decide

theorem cert50_component_1_7_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 27 cert50_seen_1_7_0 = cert50_component_1_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_7_0 cert50_layer_1_7_0 26 cert50_layer_1_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.b LColor.p 26 cert50_seen_1_7_1 = cert50_component_1_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.b LColor.p
    cert50_seen_1_7_1 cert50_layer_1_7_1_eq 26

theorem cert50_step_1_7 :
    closedCollarIndexStepBool word fiber50 1 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_7)
    (by decide) (by decide)
    (by simpa [cert50_move_1_7] using cert50_component_1_7_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_1_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_1_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_13_0 = cert50_layer_1_13_0 := by
  decide

def cert50_seen_1_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_1_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_1_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_13_1 = cert50_layer_1_13_1 := by
  decide

def cert50_seen_1_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_1_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_1_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_13_2 = cert50_layer_1_13_2 := by
  decide

def cert50_seen_1_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_1_13_3 : List ChainEdge :=
  []

theorem cert50_layer_1_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.b cert50_seen_1_13_3 = cert50_layer_1_13_3 := by
  decide

theorem cert50_component_1_13_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_1_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 27 cert50_seen_1_13_0 = cert50_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_13_0 cert50_layer_1_13_0 26 cert50_layer_1_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 26 cert50_seen_1_13_1 = cert50_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_13_1 cert50_layer_1_13_1 25 cert50_layer_1_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 25 cert50_seen_1_13_2 = cert50_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_13_2 cert50_layer_1_13_2 24 cert50_layer_1_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.b 24 cert50_seen_1_13_3 = cert50_component_1_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.b
    cert50_seen_1_13_3 cert50_layer_1_13_3_eq 24

theorem cert50_step_1_13 :
    closedCollarIndexStepBool word fiber50 1 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_13)
    (by decide) (by decide)
    (by simpa [cert50_move_1_13] using cert50_component_1_13_eq)
    (by decide) (by decide) (by decide)

def cert50_move_1_39 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_1_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_1_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_1_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_1_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_39_0 = cert50_layer_1_39_0 := by
  decide

def cert50_seen_1_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_1_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_1_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_39_1 = cert50_layer_1_39_1 := by
  decide

def cert50_seen_1_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_1_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_1_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_39_2 = cert50_layer_1_39_2 := by
  decide

def cert50_seen_1_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_1_39_3 : List ChainEdge :=
  []

theorem cert50_layer_1_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 1 [])
      LColor.r LColor.p cert50_seen_1_39_3 = cert50_layer_1_39_3 := by
  decide

theorem cert50_component_1_39_eq :
    closedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_1_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 27 cert50_seen_1_39_0 = cert50_component_1_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_39_0 cert50_layer_1_39_0 26 cert50_layer_1_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 26 cert50_seen_1_39_1 = cert50_component_1_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_39_1 cert50_layer_1_39_1 25 cert50_layer_1_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 25 cert50_seen_1_39_2 = cert50_component_1_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_39_2 cert50_layer_1_39_2 24 cert50_layer_1_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 1 [])
      LColor.r LColor.p 24 cert50_seen_1_39_3 = cert50_component_1_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 1 []) LColor.r LColor.p
    cert50_seen_1_39_3 cert50_layer_1_39_3_eq 24

theorem cert50_step_1_39 :
    closedCollarIndexStepBool word fiber50 1 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_1_39)
    (by decide) (by decide)
    (by simpa [cert50_move_1_39] using cert50_component_1_39_eq)
    (by decide) (by decide) (by decide)

def cert50_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert50_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_0 = cert50_layer_2_0_0 := by
  decide

def cert50_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_2_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_1 = cert50_layer_2_0_1 := by
  decide

def cert50_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_2_0_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_2 = cert50_layer_2_0_2 := by
  decide

def cert50_seen_2_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_2_0_3 : List ChainEdge :=
  []

theorem cert50_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_0_3 = cert50_layer_2_0_3 := by
  decide

theorem cert50_component_2_0_eq :
    closedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert50_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 27 cert50_seen_2_0_0 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_0 cert50_layer_2_0_0 26 cert50_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 26 cert50_seen_2_0_1 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_1 cert50_layer_2_0_1 25 cert50_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 25 cert50_seen_2_0_2 = cert50_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_2 cert50_layer_2_0_2 24 cert50_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 24 cert50_seen_2_0_3 = cert50_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_0_3 cert50_layer_2_0_3_eq 24

theorem cert50_step_2_0 :
    closedCollarIndexStepBool word fiber50 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_2_0)
    (by decide) (by decide)
    (by simpa [cert50_move_2_0] using cert50_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_2_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.b LColor.p cert50_seen_2_8_0 = cert50_layer_2_8_0 := by
  decide

def cert50_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_2_8_1 : List ChainEdge :=
  []

theorem cert50_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.b LColor.p cert50_seen_2_8_1 = cert50_layer_2_8_1 := by
  decide

theorem cert50_component_2_8_eq :
    closedCollarComponent word (listGetD fiber50 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.b LColor.p 27 cert50_seen_2_8_0 = cert50_component_2_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.b LColor.p
    cert50_seen_2_8_0 cert50_layer_2_8_0 26 cert50_layer_2_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.b LColor.p 26 cert50_seen_2_8_1 = cert50_component_2_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 2 []) LColor.b LColor.p
    cert50_seen_2_8_1 cert50_layer_2_8_1_eq 26

theorem cert50_step_2_8 :
    closedCollarIndexStepBool word fiber50 2 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_2_8)
    (by decide) (by decide)
    (by simpa [cert50_move_2_8] using cert50_component_2_8_eq)
    (by decide) (by decide) (by decide)

def cert50_move_2_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_2_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_2_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_14_0 = cert50_layer_2_14_0 := by
  decide

def cert50_seen_2_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_2_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_2_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_14_1 = cert50_layer_2_14_1 := by
  decide

def cert50_seen_2_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_2_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_2_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_14_2 = cert50_layer_2_14_2 := by
  decide

def cert50_seen_2_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_2_14_3 : List ChainEdge :=
  []

theorem cert50_layer_2_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.b cert50_seen_2_14_3 = cert50_layer_2_14_3 := by
  decide

theorem cert50_component_2_14_eq :
    closedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_2_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 27 cert50_seen_2_14_0 = cert50_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_14_0 cert50_layer_2_14_0 26 cert50_layer_2_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 26 cert50_seen_2_14_1 = cert50_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_14_1 cert50_layer_2_14_1 25 cert50_layer_2_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 25 cert50_seen_2_14_2 = cert50_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_14_2 cert50_layer_2_14_2 24 cert50_layer_2_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.b 24 cert50_seen_2_14_3 = cert50_component_2_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 2 []) LColor.r LColor.b
    cert50_seen_2_14_3 cert50_layer_2_14_3_eq 24

theorem cert50_step_2_14 :
    closedCollarIndexStepBool word fiber50 2 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_2_14)
    (by decide) (by decide)
    (by simpa [cert50_move_2_14] using cert50_component_2_14_eq)
    (by decide) (by decide) (by decide)

def cert50_move_2_40 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_2_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_2_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_2_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_2_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.p cert50_seen_2_40_0 = cert50_layer_2_40_0 := by
  decide

def cert50_seen_2_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_2_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_2_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.p cert50_seen_2_40_1 = cert50_layer_2_40_1 := by
  decide

def cert50_seen_2_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_2_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_2_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.p cert50_seen_2_40_2 = cert50_layer_2_40_2 := by
  decide

def cert50_seen_2_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_2_40_3 : List ChainEdge :=
  []

theorem cert50_layer_2_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 2 [])
      LColor.r LColor.p cert50_seen_2_40_3 = cert50_layer_2_40_3 := by
  decide

theorem cert50_component_2_40_eq :
    closedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_2_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.p 27 cert50_seen_2_40_0 = cert50_component_2_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.p
    cert50_seen_2_40_0 cert50_layer_2_40_0 26 cert50_layer_2_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.p 26 cert50_seen_2_40_1 = cert50_component_2_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.p
    cert50_seen_2_40_1 cert50_layer_2_40_1 25 cert50_layer_2_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.p 25 cert50_seen_2_40_2 = cert50_component_2_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 2 []) LColor.r LColor.p
    cert50_seen_2_40_2 cert50_layer_2_40_2 24 cert50_layer_2_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 2 [])
      LColor.r LColor.p 24 cert50_seen_2_40_3 = cert50_component_2_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 2 []) LColor.r LColor.p
    cert50_seen_2_40_3 cert50_layer_2_40_3_eq 24

theorem cert50_step_2_40 :
    closedCollarIndexStepBool word fiber50 2 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_2_40)
    (by decide) (by decide)
    (by simpa [cert50_move_2_40] using cert50_component_2_40_eq)
    (by decide) (by decide) (by decide)

def cert50_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert50_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_0 = cert50_layer_3_1_0 := by
  decide

def cert50_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_3_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_1 = cert50_layer_3_1_1 := by
  decide

def cert50_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_3_1_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_2 = cert50_layer_3_1_2 := by
  decide

def cert50_seen_3_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_3_1_3 : List ChainEdge :=
  []

theorem cert50_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_1_3 = cert50_layer_3_1_3 := by
  decide

theorem cert50_component_3_1_eq :
    closedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert50_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 27 cert50_seen_3_1_0 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_0 cert50_layer_3_1_0 26 cert50_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 26 cert50_seen_3_1_1 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_1 cert50_layer_3_1_1 25 cert50_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 25 cert50_seen_3_1_2 = cert50_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_2 cert50_layer_3_1_2 24 cert50_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 24 cert50_seen_3_1_3 = cert50_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_1_3 cert50_layer_3_1_3_eq 24

theorem cert50_step_3_1 :
    closedCollarIndexStepBool word fiber50 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_3_1)
    (by decide) (by decide)
    (by simpa [cert50_move_3_1] using cert50_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_3_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.b LColor.p cert50_seen_3_9_0 = cert50_layer_3_9_0 := by
  decide

def cert50_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_3_9_1 : List ChainEdge :=
  []

theorem cert50_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.b LColor.p cert50_seen_3_9_1 = cert50_layer_3_9_1 := by
  decide

theorem cert50_component_3_9_eq :
    closedCollarComponent word (listGetD fiber50 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.b LColor.p 27 cert50_seen_3_9_0 = cert50_component_3_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.b LColor.p
    cert50_seen_3_9_0 cert50_layer_3_9_0 26 cert50_layer_3_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.b LColor.p 26 cert50_seen_3_9_1 = cert50_component_3_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 3 []) LColor.b LColor.p
    cert50_seen_3_9_1 cert50_layer_3_9_1_eq 26

theorem cert50_step_3_9 :
    closedCollarIndexStepBool word fiber50 3 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_3_9)
    (by decide) (by decide)
    (by simpa [cert50_move_3_9] using cert50_component_3_9_eq)
    (by decide) (by decide) (by decide)

def cert50_move_3_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_3_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_3_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_15_0 = cert50_layer_3_15_0 := by
  decide

def cert50_seen_3_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_3_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_3_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_15_1 = cert50_layer_3_15_1 := by
  decide

def cert50_seen_3_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_3_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_3_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_15_2 = cert50_layer_3_15_2 := by
  decide

def cert50_seen_3_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_3_15_3 : List ChainEdge :=
  []

theorem cert50_layer_3_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.b cert50_seen_3_15_3 = cert50_layer_3_15_3 := by
  decide

theorem cert50_component_3_15_eq :
    closedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_3_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 27 cert50_seen_3_15_0 = cert50_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_15_0 cert50_layer_3_15_0 26 cert50_layer_3_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 26 cert50_seen_3_15_1 = cert50_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_15_1 cert50_layer_3_15_1 25 cert50_layer_3_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 25 cert50_seen_3_15_2 = cert50_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_15_2 cert50_layer_3_15_2 24 cert50_layer_3_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.b 24 cert50_seen_3_15_3 = cert50_component_3_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 3 []) LColor.r LColor.b
    cert50_seen_3_15_3 cert50_layer_3_15_3_eq 24

theorem cert50_step_3_15 :
    closedCollarIndexStepBool word fiber50 3 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_3_15)
    (by decide) (by decide)
    (by simpa [cert50_move_3_15] using cert50_component_3_15_eq)
    (by decide) (by decide) (by decide)

def cert50_move_3_41 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_3_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_3_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_3_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_3_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.p cert50_seen_3_41_0 = cert50_layer_3_41_0 := by
  decide

def cert50_seen_3_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_3_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_3_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.p cert50_seen_3_41_1 = cert50_layer_3_41_1 := by
  decide

def cert50_seen_3_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_3_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_3_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.p cert50_seen_3_41_2 = cert50_layer_3_41_2 := by
  decide

def cert50_seen_3_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_3_41_3 : List ChainEdge :=
  []

theorem cert50_layer_3_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 3 [])
      LColor.r LColor.p cert50_seen_3_41_3 = cert50_layer_3_41_3 := by
  decide

theorem cert50_component_3_41_eq :
    closedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_3_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.p 27 cert50_seen_3_41_0 = cert50_component_3_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.p
    cert50_seen_3_41_0 cert50_layer_3_41_0 26 cert50_layer_3_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.p 26 cert50_seen_3_41_1 = cert50_component_3_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.p
    cert50_seen_3_41_1 cert50_layer_3_41_1 25 cert50_layer_3_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.p 25 cert50_seen_3_41_2 = cert50_component_3_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 3 []) LColor.r LColor.p
    cert50_seen_3_41_2 cert50_layer_3_41_2 24 cert50_layer_3_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 3 [])
      LColor.r LColor.p 24 cert50_seen_3_41_3 = cert50_component_3_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 3 []) LColor.r LColor.p
    cert50_seen_3_41_3 cert50_layer_3_41_3_eq 24

theorem cert50_step_3_41 :
    closedCollarIndexStepBool word fiber50 3 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_3_41)
    (by decide) (by decide)
    (by simpa [cert50_move_3_41] using cert50_component_3_41_eq)
    (by decide) (by decide) (by decide)

def cert50_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert50_component_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_0 = cert50_layer_4_1_0 := by
  decide

def cert50_seen_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_1 = cert50_layer_4_1_1 := by
  decide

def cert50_seen_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_2 = cert50_layer_4_1_2 := by
  decide

def cert50_seen_4_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_4_1_3 : List ChainEdge :=
  []

theorem cert50_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_1_3 = cert50_layer_4_1_3 := by
  decide

theorem cert50_component_4_1_eq :
    closedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert50_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 27 cert50_seen_4_1_0 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_0 cert50_layer_4_1_0 26 cert50_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 26 cert50_seen_4_1_1 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_1 cert50_layer_4_1_1 25 cert50_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 25 cert50_seen_4_1_2 = cert50_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_2 cert50_layer_4_1_2 24 cert50_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 24 cert50_seen_4_1_3 = cert50_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_1_3 cert50_layer_4_1_3_eq 24

theorem cert50_step_4_1 :
    closedCollarIndexStepBool word fiber50 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_4_1)
    (by decide) (by decide)
    (by simpa [cert50_move_4_1] using cert50_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_4_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.b LColor.p cert50_seen_4_10_0 = cert50_layer_4_10_0 := by
  decide

def cert50_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_4_10_1 : List ChainEdge :=
  []

theorem cert50_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.b LColor.p cert50_seen_4_10_1 = cert50_layer_4_10_1 := by
  decide

theorem cert50_component_4_10_eq :
    closedCollarComponent word (listGetD fiber50 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.b LColor.p 27 cert50_seen_4_10_0 = cert50_component_4_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.b LColor.p
    cert50_seen_4_10_0 cert50_layer_4_10_0 26 cert50_layer_4_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.b LColor.p 26 cert50_seen_4_10_1 = cert50_component_4_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 4 []) LColor.b LColor.p
    cert50_seen_4_10_1 cert50_layer_4_10_1_eq 26

theorem cert50_step_4_10 :
    closedCollarIndexStepBool word fiber50 4 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_4_10)
    (by decide) (by decide)
    (by simpa [cert50_move_4_10] using cert50_component_4_10_eq)
    (by decide) (by decide) (by decide)

def cert50_move_4_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_4_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_4_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_0 = cert50_layer_4_16_0 := by
  decide

def cert50_seen_4_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_4_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_4_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_1 = cert50_layer_4_16_1 := by
  decide

def cert50_seen_4_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_4_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_4_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_2 = cert50_layer_4_16_2 := by
  decide

def cert50_seen_4_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_4_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_4_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_3 = cert50_layer_4_16_3 := by
  decide

def cert50_seen_4_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_4_16_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_4_16_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_4 = cert50_layer_4_16_4 := by
  decide

def cert50_seen_4_16_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_4_16_5 : List ChainEdge :=
  []

theorem cert50_layer_4_16_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.b cert50_seen_4_16_5 = cert50_layer_4_16_5 := by
  decide

theorem cert50_component_4_16_eq :
    closedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_4_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 27 cert50_seen_4_16_0 = cert50_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_0 cert50_layer_4_16_0 26 cert50_layer_4_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 26 cert50_seen_4_16_1 = cert50_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_1 cert50_layer_4_16_1 25 cert50_layer_4_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 25 cert50_seen_4_16_2 = cert50_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_2 cert50_layer_4_16_2 24 cert50_layer_4_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 24 cert50_seen_4_16_3 = cert50_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_3 cert50_layer_4_16_3 23 cert50_layer_4_16_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 23 cert50_seen_4_16_4 = cert50_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_4 cert50_layer_4_16_4 22 cert50_layer_4_16_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.b 22 cert50_seen_4_16_5 = cert50_component_4_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 4 []) LColor.r LColor.b
    cert50_seen_4_16_5 cert50_layer_4_16_5_eq 22

theorem cert50_step_4_16 :
    closedCollarIndexStepBool word fiber50 4 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_4_16)
    (by decide) (by decide)
    (by simpa [cert50_move_4_16] using cert50_component_4_16_eq)
    (by decide) (by decide) (by decide)

def cert50_move_4_42 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_4_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_4_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_4_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_4_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_42_0 = cert50_layer_4_42_0 := by
  decide

def cert50_seen_4_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_4_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_4_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_42_1 = cert50_layer_4_42_1 := by
  decide

def cert50_seen_4_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_4_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_4_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_42_2 = cert50_layer_4_42_2 := by
  decide

def cert50_seen_4_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_4_42_3 : List ChainEdge :=
  []

theorem cert50_layer_4_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 4 [])
      LColor.r LColor.p cert50_seen_4_42_3 = cert50_layer_4_42_3 := by
  decide

theorem cert50_component_4_42_eq :
    closedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_4_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 27 cert50_seen_4_42_0 = cert50_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_42_0 cert50_layer_4_42_0 26 cert50_layer_4_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 26 cert50_seen_4_42_1 = cert50_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_42_1 cert50_layer_4_42_1 25 cert50_layer_4_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 25 cert50_seen_4_42_2 = cert50_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_42_2 cert50_layer_4_42_2 24 cert50_layer_4_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 4 [])
      LColor.r LColor.p 24 cert50_seen_4_42_3 = cert50_component_4_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 4 []) LColor.r LColor.p
    cert50_seen_4_42_3 cert50_layer_4_42_3_eq 24

theorem cert50_step_4_42 :
    closedCollarIndexStepBool word fiber50 4 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_4_42)
    (by decide) (by decide)
    (by simpa [cert50_move_4_42] using cert50_component_4_42_eq)
    (by decide) (by decide) (by decide)

def cert50_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert50_component_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_seen_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_0 = cert50_layer_5_0_0 := by
  decide

def cert50_seen_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_1 = cert50_layer_5_0_1 := by
  decide

def cert50_seen_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_2 = cert50_layer_5_0_2 := by
  decide

def cert50_seen_5_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_5_0_3 : List ChainEdge :=
  []

theorem cert50_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_0_3 = cert50_layer_5_0_3 := by
  decide

theorem cert50_component_5_0_eq :
    closedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert50_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 27 cert50_seen_5_0_0 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_0 cert50_layer_5_0_0 26 cert50_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 26 cert50_seen_5_0_1 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_1 cert50_layer_5_0_1 25 cert50_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 25 cert50_seen_5_0_2 = cert50_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_2 cert50_layer_5_0_2 24 cert50_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 24 cert50_seen_5_0_3 = cert50_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_0_3 cert50_layer_5_0_3_eq 24

theorem cert50_step_5_0 :
    closedCollarIndexStepBool word fiber50 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_5_0)
    (by decide) (by decide)
    (by simpa [cert50_move_5_0] using cert50_component_5_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_5_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.b LColor.p cert50_seen_5_11_0 = cert50_layer_5_11_0 := by
  decide

def cert50_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_5_11_1 : List ChainEdge :=
  []

theorem cert50_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.b LColor.p cert50_seen_5_11_1 = cert50_layer_5_11_1 := by
  decide

theorem cert50_component_5_11_eq :
    closedCollarComponent word (listGetD fiber50 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.b LColor.p 27 cert50_seen_5_11_0 = cert50_component_5_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.b LColor.p
    cert50_seen_5_11_0 cert50_layer_5_11_0 26 cert50_layer_5_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.b LColor.p 26 cert50_seen_5_11_1 = cert50_component_5_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 5 []) LColor.b LColor.p
    cert50_seen_5_11_1 cert50_layer_5_11_1_eq 26

theorem cert50_step_5_11 :
    closedCollarIndexStepBool word fiber50 5 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_5_11)
    (by decide) (by decide)
    (by simpa [cert50_move_5_11] using cert50_component_5_11_eq)
    (by decide) (by decide) (by decide)

def cert50_move_5_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_5_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_5_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_0 = cert50_layer_5_17_0 := by
  decide

def cert50_seen_5_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_5_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_5_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_1 = cert50_layer_5_17_1 := by
  decide

def cert50_seen_5_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_5_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_5_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_2 = cert50_layer_5_17_2 := by
  decide

def cert50_seen_5_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_5_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_5_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_3 = cert50_layer_5_17_3 := by
  decide

def cert50_seen_5_17_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_5_17_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_5_17_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_4 = cert50_layer_5_17_4 := by
  decide

def cert50_seen_5_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_5_17_5 : List ChainEdge :=
  []

theorem cert50_layer_5_17_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.b cert50_seen_5_17_5 = cert50_layer_5_17_5 := by
  decide

theorem cert50_component_5_17_eq :
    closedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_5_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 27 cert50_seen_5_17_0 = cert50_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_0 cert50_layer_5_17_0 26 cert50_layer_5_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 26 cert50_seen_5_17_1 = cert50_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_1 cert50_layer_5_17_1 25 cert50_layer_5_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 25 cert50_seen_5_17_2 = cert50_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_2 cert50_layer_5_17_2 24 cert50_layer_5_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 24 cert50_seen_5_17_3 = cert50_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_3 cert50_layer_5_17_3 23 cert50_layer_5_17_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 23 cert50_seen_5_17_4 = cert50_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_4 cert50_layer_5_17_4 22 cert50_layer_5_17_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.b 22 cert50_seen_5_17_5 = cert50_component_5_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 5 []) LColor.r LColor.b
    cert50_seen_5_17_5 cert50_layer_5_17_5_eq 22

theorem cert50_step_5_17 :
    closedCollarIndexStepBool word fiber50 5 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_5_17)
    (by decide) (by decide)
    (by simpa [cert50_move_5_17] using cert50_component_5_17_eq)
    (by decide) (by decide) (by decide)

def cert50_move_5_43 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_5_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_5_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_5_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_5_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_43_0 = cert50_layer_5_43_0 := by
  decide

def cert50_seen_5_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_5_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_5_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_43_1 = cert50_layer_5_43_1 := by
  decide

def cert50_seen_5_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_5_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_5_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_43_2 = cert50_layer_5_43_2 := by
  decide

def cert50_seen_5_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_5_43_3 : List ChainEdge :=
  []

theorem cert50_layer_5_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 5 [])
      LColor.r LColor.p cert50_seen_5_43_3 = cert50_layer_5_43_3 := by
  decide

theorem cert50_component_5_43_eq :
    closedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_5_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 27 cert50_seen_5_43_0 = cert50_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_43_0 cert50_layer_5_43_0 26 cert50_layer_5_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 26 cert50_seen_5_43_1 = cert50_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_43_1 cert50_layer_5_43_1 25 cert50_layer_5_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 25 cert50_seen_5_43_2 = cert50_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_43_2 cert50_layer_5_43_2 24 cert50_layer_5_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 5 [])
      LColor.r LColor.p 24 cert50_seen_5_43_3 = cert50_component_5_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 5 []) LColor.r LColor.p
    cert50_seen_5_43_3 cert50_layer_5_43_3_eq 24

theorem cert50_step_5_43 :
    closedCollarIndexStepBool word fiber50 5 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_5_43)
    (by decide) (by decide)
    (by simpa [cert50_move_5_43] using cert50_component_5_43_eq)
    (by decide) (by decide) (by decide)

def cert50_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.b LColor.p cert50_seen_6_0_0 = cert50_layer_6_0_0 := by
  decide

def cert50_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_6_0_1 : List ChainEdge :=
  []

theorem cert50_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.b LColor.p cert50_seen_6_0_1 = cert50_layer_6_0_1 := by
  decide

theorem cert50_component_6_0_eq :
    closedCollarComponent word (listGetD fiber50 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.b LColor.p 27 cert50_seen_6_0_0 = cert50_component_6_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.b LColor.p
    cert50_seen_6_0_0 cert50_layer_6_0_0 26 cert50_layer_6_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.b LColor.p 26 cert50_seen_6_0_1 = cert50_component_6_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 6 []) LColor.b LColor.p
    cert50_seen_6_0_1 cert50_layer_6_0_1_eq 26

theorem cert50_step_6_0 :
    closedCollarIndexStepBool word fiber50 6 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_6_0)
    (by decide) (by decide)
    (by simpa [cert50_move_6_0] using cert50_component_6_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_6_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_6_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_6_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.b cert50_seen_6_18_0 = cert50_layer_6_18_0 := by
  decide

def cert50_seen_6_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_6_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_6_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.b cert50_seen_6_18_1 = cert50_layer_6_18_1 := by
  decide

def cert50_seen_6_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_6_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_6_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.b cert50_seen_6_18_2 = cert50_layer_6_18_2 := by
  decide

def cert50_seen_6_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_6_18_3 : List ChainEdge :=
  []

theorem cert50_layer_6_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.b cert50_seen_6_18_3 = cert50_layer_6_18_3 := by
  decide

theorem cert50_component_6_18_eq :
    closedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_6_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.b 27 cert50_seen_6_18_0 = cert50_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.b
    cert50_seen_6_18_0 cert50_layer_6_18_0 26 cert50_layer_6_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.b 26 cert50_seen_6_18_1 = cert50_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.b
    cert50_seen_6_18_1 cert50_layer_6_18_1 25 cert50_layer_6_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.b 25 cert50_seen_6_18_2 = cert50_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.b
    cert50_seen_6_18_2 cert50_layer_6_18_2 24 cert50_layer_6_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.b 24 cert50_seen_6_18_3 = cert50_component_6_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 6 []) LColor.r LColor.b
    cert50_seen_6_18_3 cert50_layer_6_18_3_eq 24

theorem cert50_step_6_18 :
    closedCollarIndexStepBool word fiber50 6 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_6_18)
    (by decide) (by decide)
    (by simpa [cert50_move_6_18] using cert50_component_6_18_eq)
    (by decide) (by decide) (by decide)

def cert50_move_6_32 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_6_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_6_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_6_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_6_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.p cert50_seen_6_32_0 = cert50_layer_6_32_0 := by
  decide

def cert50_seen_6_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_6_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_6_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.p cert50_seen_6_32_1 = cert50_layer_6_32_1 := by
  decide

def cert50_seen_6_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_6_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_6_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.p cert50_seen_6_32_2 = cert50_layer_6_32_2 := by
  decide

def cert50_seen_6_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_6_32_3 : List ChainEdge :=
  []

theorem cert50_layer_6_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 6 [])
      LColor.r LColor.p cert50_seen_6_32_3 = cert50_layer_6_32_3 := by
  decide

theorem cert50_component_6_32_eq :
    closedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_6_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.p 27 cert50_seen_6_32_0 = cert50_component_6_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.p
    cert50_seen_6_32_0 cert50_layer_6_32_0 26 cert50_layer_6_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.p 26 cert50_seen_6_32_1 = cert50_component_6_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.p
    cert50_seen_6_32_1 cert50_layer_6_32_1 25 cert50_layer_6_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.p 25 cert50_seen_6_32_2 = cert50_component_6_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 6 []) LColor.r LColor.p
    cert50_seen_6_32_2 cert50_layer_6_32_2 24 cert50_layer_6_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 6 [])
      LColor.r LColor.p 24 cert50_seen_6_32_3 = cert50_component_6_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 6 []) LColor.r LColor.p
    cert50_seen_6_32_3 cert50_layer_6_32_3_eq 24

theorem cert50_step_6_32 :
    closedCollarIndexStepBool word fiber50 6 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_6_32)
    (by decide) (by decide)
    (by simpa [cert50_move_6_32] using cert50_component_6_32_eq)
    (by decide) (by decide) (by decide)

def cert50_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.b LColor.p cert50_seen_7_1_0 = cert50_layer_7_1_0 := by
  decide

def cert50_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_7_1_1 : List ChainEdge :=
  []

theorem cert50_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.b LColor.p cert50_seen_7_1_1 = cert50_layer_7_1_1 := by
  decide

theorem cert50_component_7_1_eq :
    closedCollarComponent word (listGetD fiber50 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.b LColor.p 27 cert50_seen_7_1_0 = cert50_component_7_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.b LColor.p
    cert50_seen_7_1_0 cert50_layer_7_1_0 26 cert50_layer_7_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.b LColor.p 26 cert50_seen_7_1_1 = cert50_component_7_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 7 []) LColor.b LColor.p
    cert50_seen_7_1_1 cert50_layer_7_1_1_eq 26

theorem cert50_step_7_1 :
    closedCollarIndexStepBool word fiber50 7 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_7_1)
    (by decide) (by decide)
    (by simpa [cert50_move_7_1] using cert50_component_7_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_7_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_7_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_7_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.b cert50_seen_7_19_0 = cert50_layer_7_19_0 := by
  decide

def cert50_seen_7_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_7_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_7_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.b cert50_seen_7_19_1 = cert50_layer_7_19_1 := by
  decide

def cert50_seen_7_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_7_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_7_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.b cert50_seen_7_19_2 = cert50_layer_7_19_2 := by
  decide

def cert50_seen_7_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_7_19_3 : List ChainEdge :=
  []

theorem cert50_layer_7_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.b cert50_seen_7_19_3 = cert50_layer_7_19_3 := by
  decide

theorem cert50_component_7_19_eq :
    closedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_7_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.b 27 cert50_seen_7_19_0 = cert50_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.b
    cert50_seen_7_19_0 cert50_layer_7_19_0 26 cert50_layer_7_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.b 26 cert50_seen_7_19_1 = cert50_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.b
    cert50_seen_7_19_1 cert50_layer_7_19_1 25 cert50_layer_7_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.b 25 cert50_seen_7_19_2 = cert50_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.b
    cert50_seen_7_19_2 cert50_layer_7_19_2 24 cert50_layer_7_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.b 24 cert50_seen_7_19_3 = cert50_component_7_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 7 []) LColor.r LColor.b
    cert50_seen_7_19_3 cert50_layer_7_19_3_eq 24

theorem cert50_step_7_19 :
    closedCollarIndexStepBool word fiber50 7 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_7_19)
    (by decide) (by decide)
    (by simpa [cert50_move_7_19] using cert50_component_7_19_eq)
    (by decide) (by decide) (by decide)

def cert50_move_7_33 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_7_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_7_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_7_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_7_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.p cert50_seen_7_33_0 = cert50_layer_7_33_0 := by
  decide

def cert50_seen_7_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_7_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_7_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.p cert50_seen_7_33_1 = cert50_layer_7_33_1 := by
  decide

def cert50_seen_7_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_7_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_7_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.p cert50_seen_7_33_2 = cert50_layer_7_33_2 := by
  decide

def cert50_seen_7_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_7_33_3 : List ChainEdge :=
  []

theorem cert50_layer_7_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 7 [])
      LColor.r LColor.p cert50_seen_7_33_3 = cert50_layer_7_33_3 := by
  decide

theorem cert50_component_7_33_eq :
    closedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_7_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.p 27 cert50_seen_7_33_0 = cert50_component_7_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.p
    cert50_seen_7_33_0 cert50_layer_7_33_0 26 cert50_layer_7_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.p 26 cert50_seen_7_33_1 = cert50_component_7_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.p
    cert50_seen_7_33_1 cert50_layer_7_33_1 25 cert50_layer_7_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.p 25 cert50_seen_7_33_2 = cert50_component_7_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 7 []) LColor.r LColor.p
    cert50_seen_7_33_2 cert50_layer_7_33_2 24 cert50_layer_7_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 7 [])
      LColor.r LColor.p 24 cert50_seen_7_33_3 = cert50_component_7_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 7 []) LColor.r LColor.p
    cert50_seen_7_33_3 cert50_layer_7_33_3_eq 24

theorem cert50_step_7_33 :
    closedCollarIndexStepBool word fiber50 7 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_7_33)
    (by decide) (by decide)
    (by simpa [cert50_move_7_33] using cert50_component_7_33_eq)
    (by decide) (by decide) (by decide)

def cert50_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.b LColor.p cert50_seen_8_2_0 = cert50_layer_8_2_0 := by
  decide

def cert50_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_8_2_1 : List ChainEdge :=
  []

theorem cert50_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.b LColor.p cert50_seen_8_2_1 = cert50_layer_8_2_1 := by
  decide

theorem cert50_component_8_2_eq :
    closedCollarComponent word (listGetD fiber50 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.b LColor.p 27 cert50_seen_8_2_0 = cert50_component_8_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.b LColor.p
    cert50_seen_8_2_0 cert50_layer_8_2_0 26 cert50_layer_8_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.b LColor.p 26 cert50_seen_8_2_1 = cert50_component_8_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 8 []) LColor.b LColor.p
    cert50_seen_8_2_1 cert50_layer_8_2_1_eq 26

theorem cert50_step_8_2 :
    closedCollarIndexStepBool word fiber50 8 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_8_2)
    (by decide) (by decide)
    (by simpa [cert50_move_8_2] using cert50_component_8_2_eq)
    (by decide) (by decide) (by decide)

def cert50_move_8_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_8_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_8_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.b cert50_seen_8_20_0 = cert50_layer_8_20_0 := by
  decide

def cert50_seen_8_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_8_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_8_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.b cert50_seen_8_20_1 = cert50_layer_8_20_1 := by
  decide

def cert50_seen_8_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_8_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_8_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.b cert50_seen_8_20_2 = cert50_layer_8_20_2 := by
  decide

def cert50_seen_8_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_8_20_3 : List ChainEdge :=
  []

theorem cert50_layer_8_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.b cert50_seen_8_20_3 = cert50_layer_8_20_3 := by
  decide

theorem cert50_component_8_20_eq :
    closedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_8_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.b 27 cert50_seen_8_20_0 = cert50_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.b
    cert50_seen_8_20_0 cert50_layer_8_20_0 26 cert50_layer_8_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.b 26 cert50_seen_8_20_1 = cert50_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.b
    cert50_seen_8_20_1 cert50_layer_8_20_1 25 cert50_layer_8_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.b 25 cert50_seen_8_20_2 = cert50_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.b
    cert50_seen_8_20_2 cert50_layer_8_20_2 24 cert50_layer_8_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.b 24 cert50_seen_8_20_3 = cert50_component_8_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 8 []) LColor.r LColor.b
    cert50_seen_8_20_3 cert50_layer_8_20_3_eq 24

theorem cert50_step_8_20 :
    closedCollarIndexStepBool word fiber50 8 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_8_20)
    (by decide) (by decide)
    (by simpa [cert50_move_8_20] using cert50_component_8_20_eq)
    (by decide) (by decide) (by decide)

def cert50_move_8_34 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_8_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_8_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_8_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_8_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.p cert50_seen_8_34_0 = cert50_layer_8_34_0 := by
  decide

def cert50_seen_8_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_8_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_8_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.p cert50_seen_8_34_1 = cert50_layer_8_34_1 := by
  decide

def cert50_seen_8_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_8_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_8_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.p cert50_seen_8_34_2 = cert50_layer_8_34_2 := by
  decide

def cert50_seen_8_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_8_34_3 : List ChainEdge :=
  []

theorem cert50_layer_8_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 8 [])
      LColor.r LColor.p cert50_seen_8_34_3 = cert50_layer_8_34_3 := by
  decide

theorem cert50_component_8_34_eq :
    closedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_8_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.p 27 cert50_seen_8_34_0 = cert50_component_8_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.p
    cert50_seen_8_34_0 cert50_layer_8_34_0 26 cert50_layer_8_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.p 26 cert50_seen_8_34_1 = cert50_component_8_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.p
    cert50_seen_8_34_1 cert50_layer_8_34_1 25 cert50_layer_8_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.p 25 cert50_seen_8_34_2 = cert50_component_8_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 8 []) LColor.r LColor.p
    cert50_seen_8_34_2 cert50_layer_8_34_2 24 cert50_layer_8_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 8 [])
      LColor.r LColor.p 24 cert50_seen_8_34_3 = cert50_component_8_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 8 []) LColor.r LColor.p
    cert50_seen_8_34_3 cert50_layer_8_34_3_eq 24

theorem cert50_step_8_34 :
    closedCollarIndexStepBool word fiber50 8 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_8_34)
    (by decide) (by decide)
    (by simpa [cert50_move_8_34] using cert50_component_8_34_eq)
    (by decide) (by decide) (by decide)

def cert50_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.b LColor.p cert50_seen_9_3_0 = cert50_layer_9_3_0 := by
  decide

def cert50_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_9_3_1 : List ChainEdge :=
  []

theorem cert50_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.b LColor.p cert50_seen_9_3_1 = cert50_layer_9_3_1 := by
  decide

theorem cert50_component_9_3_eq :
    closedCollarComponent word (listGetD fiber50 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.b LColor.p 27 cert50_seen_9_3_0 = cert50_component_9_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.b LColor.p
    cert50_seen_9_3_0 cert50_layer_9_3_0 26 cert50_layer_9_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.b LColor.p 26 cert50_seen_9_3_1 = cert50_component_9_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 9 []) LColor.b LColor.p
    cert50_seen_9_3_1 cert50_layer_9_3_1_eq 26

theorem cert50_step_9_3 :
    closedCollarIndexStepBool word fiber50 9 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_9_3)
    (by decide) (by decide)
    (by simpa [cert50_move_9_3] using cert50_component_9_3_eq)
    (by decide) (by decide) (by decide)

def cert50_move_9_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_9_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_9_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.b cert50_seen_9_21_0 = cert50_layer_9_21_0 := by
  decide

def cert50_seen_9_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_9_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_9_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.b cert50_seen_9_21_1 = cert50_layer_9_21_1 := by
  decide

def cert50_seen_9_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_9_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_9_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.b cert50_seen_9_21_2 = cert50_layer_9_21_2 := by
  decide

def cert50_seen_9_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_9_21_3 : List ChainEdge :=
  []

theorem cert50_layer_9_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.b cert50_seen_9_21_3 = cert50_layer_9_21_3 := by
  decide

theorem cert50_component_9_21_eq :
    closedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_9_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.b 27 cert50_seen_9_21_0 = cert50_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.b
    cert50_seen_9_21_0 cert50_layer_9_21_0 26 cert50_layer_9_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.b 26 cert50_seen_9_21_1 = cert50_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.b
    cert50_seen_9_21_1 cert50_layer_9_21_1 25 cert50_layer_9_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.b 25 cert50_seen_9_21_2 = cert50_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.b
    cert50_seen_9_21_2 cert50_layer_9_21_2 24 cert50_layer_9_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.b 24 cert50_seen_9_21_3 = cert50_component_9_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 9 []) LColor.r LColor.b
    cert50_seen_9_21_3 cert50_layer_9_21_3_eq 24

theorem cert50_step_9_21 :
    closedCollarIndexStepBool word fiber50 9 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_9_21)
    (by decide) (by decide)
    (by simpa [cert50_move_9_21] using cert50_component_9_21_eq)
    (by decide) (by decide) (by decide)

def cert50_move_9_35 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_9_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_9_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_9_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_9_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.p cert50_seen_9_35_0 = cert50_layer_9_35_0 := by
  decide

def cert50_seen_9_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_9_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_9_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.p cert50_seen_9_35_1 = cert50_layer_9_35_1 := by
  decide

def cert50_seen_9_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_9_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_9_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.p cert50_seen_9_35_2 = cert50_layer_9_35_2 := by
  decide

def cert50_seen_9_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_9_35_3 : List ChainEdge :=
  []

theorem cert50_layer_9_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 9 [])
      LColor.r LColor.p cert50_seen_9_35_3 = cert50_layer_9_35_3 := by
  decide

theorem cert50_component_9_35_eq :
    closedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_9_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.p 27 cert50_seen_9_35_0 = cert50_component_9_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.p
    cert50_seen_9_35_0 cert50_layer_9_35_0 26 cert50_layer_9_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.p 26 cert50_seen_9_35_1 = cert50_component_9_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.p
    cert50_seen_9_35_1 cert50_layer_9_35_1 25 cert50_layer_9_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.p 25 cert50_seen_9_35_2 = cert50_component_9_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 9 []) LColor.r LColor.p
    cert50_seen_9_35_2 cert50_layer_9_35_2 24 cert50_layer_9_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 9 [])
      LColor.r LColor.p 24 cert50_seen_9_35_3 = cert50_component_9_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 9 []) LColor.r LColor.p
    cert50_seen_9_35_3 cert50_layer_9_35_3_eq 24

theorem cert50_step_9_35 :
    closedCollarIndexStepBool word fiber50 9 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_9_35)
    (by decide) (by decide)
    (by simpa [cert50_move_9_35] using cert50_component_9_35_eq)
    (by decide) (by decide) (by decide)

def cert50_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.b LColor.p cert50_seen_10_4_0 = cert50_layer_10_4_0 := by
  decide

def cert50_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_10_4_1 : List ChainEdge :=
  []

theorem cert50_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.b LColor.p cert50_seen_10_4_1 = cert50_layer_10_4_1 := by
  decide

theorem cert50_component_10_4_eq :
    closedCollarComponent word (listGetD fiber50 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.b LColor.p 27 cert50_seen_10_4_0 = cert50_component_10_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.b LColor.p
    cert50_seen_10_4_0 cert50_layer_10_4_0 26 cert50_layer_10_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.b LColor.p 26 cert50_seen_10_4_1 = cert50_component_10_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 10 []) LColor.b LColor.p
    cert50_seen_10_4_1 cert50_layer_10_4_1_eq 26

theorem cert50_step_10_4 :
    closedCollarIndexStepBool word fiber50 10 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_10_4)
    (by decide) (by decide)
    (by simpa [cert50_move_10_4] using cert50_component_10_4_eq)
    (by decide) (by decide) (by decide)

def cert50_move_10_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_10_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_10_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_0 = cert50_layer_10_22_0 := by
  decide

def cert50_seen_10_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_10_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_10_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_1 = cert50_layer_10_22_1 := by
  decide

def cert50_seen_10_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_10_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_10_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_2 = cert50_layer_10_22_2 := by
  decide

def cert50_seen_10_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_10_22_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_10_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_3 = cert50_layer_10_22_3 := by
  decide

def cert50_seen_10_22_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_10_22_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_10_22_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_4 = cert50_layer_10_22_4 := by
  decide

def cert50_seen_10_22_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_10_22_5 : List ChainEdge :=
  []

theorem cert50_layer_10_22_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.b cert50_seen_10_22_5 = cert50_layer_10_22_5 := by
  decide

theorem cert50_component_10_22_eq :
    closedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_10_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 27 cert50_seen_10_22_0 = cert50_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_0 cert50_layer_10_22_0 26 cert50_layer_10_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 26 cert50_seen_10_22_1 = cert50_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_1 cert50_layer_10_22_1 25 cert50_layer_10_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 25 cert50_seen_10_22_2 = cert50_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_2 cert50_layer_10_22_2 24 cert50_layer_10_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 24 cert50_seen_10_22_3 = cert50_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_3 cert50_layer_10_22_3 23 cert50_layer_10_22_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 23 cert50_seen_10_22_4 = cert50_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_4 cert50_layer_10_22_4 22 cert50_layer_10_22_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.b 22 cert50_seen_10_22_5 = cert50_component_10_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 10 []) LColor.r LColor.b
    cert50_seen_10_22_5 cert50_layer_10_22_5_eq 22

theorem cert50_step_10_22 :
    closedCollarIndexStepBool word fiber50 10 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_10_22)
    (by decide) (by decide)
    (by simpa [cert50_move_10_22] using cert50_component_10_22_eq)
    (by decide) (by decide) (by decide)

def cert50_move_10_36 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_10_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_10_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_10_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_10_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.p cert50_seen_10_36_0 = cert50_layer_10_36_0 := by
  decide

def cert50_seen_10_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_10_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_10_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.p cert50_seen_10_36_1 = cert50_layer_10_36_1 := by
  decide

def cert50_seen_10_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_10_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_10_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.p cert50_seen_10_36_2 = cert50_layer_10_36_2 := by
  decide

def cert50_seen_10_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_10_36_3 : List ChainEdge :=
  []

theorem cert50_layer_10_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 10 [])
      LColor.r LColor.p cert50_seen_10_36_3 = cert50_layer_10_36_3 := by
  decide

theorem cert50_component_10_36_eq :
    closedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_10_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.p 27 cert50_seen_10_36_0 = cert50_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.p
    cert50_seen_10_36_0 cert50_layer_10_36_0 26 cert50_layer_10_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.p 26 cert50_seen_10_36_1 = cert50_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.p
    cert50_seen_10_36_1 cert50_layer_10_36_1 25 cert50_layer_10_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.p 25 cert50_seen_10_36_2 = cert50_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 10 []) LColor.r LColor.p
    cert50_seen_10_36_2 cert50_layer_10_36_2 24 cert50_layer_10_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 10 [])
      LColor.r LColor.p 24 cert50_seen_10_36_3 = cert50_component_10_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 10 []) LColor.r LColor.p
    cert50_seen_10_36_3 cert50_layer_10_36_3_eq 24

theorem cert50_step_10_36 :
    closedCollarIndexStepBool word fiber50 10 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_10_36)
    (by decide) (by decide)
    (by simpa [cert50_move_10_36] using cert50_component_10_36_eq)
    (by decide) (by decide) (by decide)

def cert50_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert50_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert50_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.b LColor.p cert50_seen_11_5_0 = cert50_layer_11_5_0 := by
  decide

def cert50_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_11_5_1 : List ChainEdge :=
  []

theorem cert50_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.b LColor.p cert50_seen_11_5_1 = cert50_layer_11_5_1 := by
  decide

theorem cert50_component_11_5_eq :
    closedCollarComponent word (listGetD fiber50 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert50_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.b LColor.p 27 cert50_seen_11_5_0 = cert50_component_11_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.b LColor.p
    cert50_seen_11_5_0 cert50_layer_11_5_0 26 cert50_layer_11_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.b LColor.p 26 cert50_seen_11_5_1 = cert50_component_11_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 11 []) LColor.b LColor.p
    cert50_seen_11_5_1 cert50_layer_11_5_1_eq 26

theorem cert50_step_11_5 :
    closedCollarIndexStepBool word fiber50 11 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_11_5)
    (by decide) (by decide)
    (by simpa [cert50_move_11_5] using cert50_component_11_5_eq)
    (by decide) (by decide) (by decide)

def cert50_move_11_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_11_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_11_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_0 = cert50_layer_11_23_0 := by
  decide

def cert50_seen_11_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_11_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_11_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_1 = cert50_layer_11_23_1 := by
  decide

def cert50_seen_11_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_11_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_11_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_2 = cert50_layer_11_23_2 := by
  decide

def cert50_seen_11_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_11_23_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_11_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_3 = cert50_layer_11_23_3 := by
  decide

def cert50_seen_11_23_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_11_23_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_11_23_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_4 = cert50_layer_11_23_4 := by
  decide

def cert50_seen_11_23_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_11_23_5 : List ChainEdge :=
  []

theorem cert50_layer_11_23_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.b cert50_seen_11_23_5 = cert50_layer_11_23_5 := by
  decide

theorem cert50_component_11_23_eq :
    closedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_11_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 27 cert50_seen_11_23_0 = cert50_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_0 cert50_layer_11_23_0 26 cert50_layer_11_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 26 cert50_seen_11_23_1 = cert50_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_1 cert50_layer_11_23_1 25 cert50_layer_11_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 25 cert50_seen_11_23_2 = cert50_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_2 cert50_layer_11_23_2 24 cert50_layer_11_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 24 cert50_seen_11_23_3 = cert50_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_3 cert50_layer_11_23_3 23 cert50_layer_11_23_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 23 cert50_seen_11_23_4 = cert50_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_4 cert50_layer_11_23_4 22 cert50_layer_11_23_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.b 22 cert50_seen_11_23_5 = cert50_component_11_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 11 []) LColor.r LColor.b
    cert50_seen_11_23_5 cert50_layer_11_23_5_eq 22

theorem cert50_step_11_23 :
    closedCollarIndexStepBool word fiber50 11 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_11_23)
    (by decide) (by decide)
    (by simpa [cert50_move_11_23] using cert50_component_11_23_eq)
    (by decide) (by decide) (by decide)

def cert50_move_11_37 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_11_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_11_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_11_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_11_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.p cert50_seen_11_37_0 = cert50_layer_11_37_0 := by
  decide

def cert50_seen_11_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_11_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_11_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.p cert50_seen_11_37_1 = cert50_layer_11_37_1 := by
  decide

def cert50_seen_11_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_11_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_11_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.p cert50_seen_11_37_2 = cert50_layer_11_37_2 := by
  decide

def cert50_seen_11_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_11_37_3 : List ChainEdge :=
  []

theorem cert50_layer_11_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 11 [])
      LColor.r LColor.p cert50_seen_11_37_3 = cert50_layer_11_37_3 := by
  decide

theorem cert50_component_11_37_eq :
    closedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_11_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.p 27 cert50_seen_11_37_0 = cert50_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.p
    cert50_seen_11_37_0 cert50_layer_11_37_0 26 cert50_layer_11_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.p 26 cert50_seen_11_37_1 = cert50_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.p
    cert50_seen_11_37_1 cert50_layer_11_37_1 25 cert50_layer_11_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.p 25 cert50_seen_11_37_2 = cert50_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 11 []) LColor.r LColor.p
    cert50_seen_11_37_2 cert50_layer_11_37_2 24 cert50_layer_11_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 11 [])
      LColor.r LColor.p 24 cert50_seen_11_37_3 = cert50_component_11_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 11 []) LColor.r LColor.p
    cert50_seen_11_37_3 cert50_layer_11_37_3_eq 24

theorem cert50_step_11_37 :
    closedCollarIndexStepBool word fiber50 11 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_11_37)
    (by decide) (by decide)
    (by simpa [cert50_move_11_37] using cert50_component_11_37_eq)
    (by decide) (by decide) (by decide)

def cert50_move_12_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_12_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.b cert50_seen_12_0_0 = cert50_layer_12_0_0 := by
  decide

def cert50_seen_12_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_12_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_12_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.b cert50_seen_12_0_1 = cert50_layer_12_0_1 := by
  decide

def cert50_seen_12_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_12_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_12_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.b cert50_seen_12_0_2 = cert50_layer_12_0_2 := by
  decide

def cert50_seen_12_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_12_0_3 : List ChainEdge :=
  []

theorem cert50_layer_12_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.b cert50_seen_12_0_3 = cert50_layer_12_0_3 := by
  decide

theorem cert50_component_12_0_eq :
    closedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_12_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.b 27 cert50_seen_12_0_0 = cert50_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.b
    cert50_seen_12_0_0 cert50_layer_12_0_0 26 cert50_layer_12_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.b 26 cert50_seen_12_0_1 = cert50_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.b
    cert50_seen_12_0_1 cert50_layer_12_0_1 25 cert50_layer_12_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.b 25 cert50_seen_12_0_2 = cert50_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.b
    cert50_seen_12_0_2 cert50_layer_12_0_2 24 cert50_layer_12_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.b 24 cert50_seen_12_0_3 = cert50_component_12_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 12 []) LColor.r LColor.b
    cert50_seen_12_0_3 cert50_layer_12_0_3_eq 24

theorem cert50_step_12_0 :
    closedCollarIndexStepBool word fiber50 12 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_12_0)
    (by decide) (by decide)
    (by simpa [cert50_move_12_0] using cert50_component_12_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_12_27 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_12_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_seen_12_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_12_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_12_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_0 = cert50_layer_12_27_0 := by
  decide

def cert50_seen_12_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_12_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_12_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_1 = cert50_layer_12_27_1 := by
  decide

def cert50_seen_12_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_12_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_12_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_2 = cert50_layer_12_27_2 := by
  decide

def cert50_seen_12_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_12_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_12_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_3 = cert50_layer_12_27_3 := by
  decide

def cert50_seen_12_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_12_27_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_12_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_4 = cert50_layer_12_27_4 := by
  decide

def cert50_seen_12_27_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_12_27_5 : List ChainEdge :=
  []

theorem cert50_layer_12_27_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 12 [])
      LColor.r LColor.p cert50_seen_12_27_5 = cert50_layer_12_27_5 := by
  decide

theorem cert50_component_12_27_eq :
    closedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_12_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 27 cert50_seen_12_27_0 = cert50_component_12_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_0 cert50_layer_12_27_0 26 cert50_layer_12_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 26 cert50_seen_12_27_1 = cert50_component_12_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_1 cert50_layer_12_27_1 25 cert50_layer_12_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 25 cert50_seen_12_27_2 = cert50_component_12_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_2 cert50_layer_12_27_2 24 cert50_layer_12_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 24 cert50_seen_12_27_3 = cert50_component_12_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_3 cert50_layer_12_27_3 23 cert50_layer_12_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 23 cert50_seen_12_27_4 = cert50_component_12_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_4 cert50_layer_12_27_4 22 cert50_layer_12_27_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 12 [])
      LColor.r LColor.p 22 cert50_seen_12_27_5 = cert50_component_12_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 12 []) LColor.r LColor.p
    cert50_seen_12_27_5 cert50_layer_12_27_5_eq 22

theorem cert50_step_12_27 :
    closedCollarIndexStepBool word fiber50 12 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_12_27)
    (by decide) (by decide)
    (by simpa [cert50_move_12_27] using cert50_component_12_27_eq)
    (by decide) (by decide) (by decide)

def cert50_move_13_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_13_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.b cert50_seen_13_1_0 = cert50_layer_13_1_0 := by
  decide

def cert50_seen_13_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_13_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_13_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.b cert50_seen_13_1_1 = cert50_layer_13_1_1 := by
  decide

def cert50_seen_13_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_13_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_13_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.b cert50_seen_13_1_2 = cert50_layer_13_1_2 := by
  decide

def cert50_seen_13_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_13_1_3 : List ChainEdge :=
  []

theorem cert50_layer_13_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.b cert50_seen_13_1_3 = cert50_layer_13_1_3 := by
  decide

theorem cert50_component_13_1_eq :
    closedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_13_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.b 27 cert50_seen_13_1_0 = cert50_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.b
    cert50_seen_13_1_0 cert50_layer_13_1_0 26 cert50_layer_13_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.b 26 cert50_seen_13_1_1 = cert50_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.b
    cert50_seen_13_1_1 cert50_layer_13_1_1 25 cert50_layer_13_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.b 25 cert50_seen_13_1_2 = cert50_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.b
    cert50_seen_13_1_2 cert50_layer_13_1_2 24 cert50_layer_13_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.b 24 cert50_seen_13_1_3 = cert50_component_13_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 13 []) LColor.r LColor.b
    cert50_seen_13_1_3 cert50_layer_13_1_3_eq 24

theorem cert50_step_13_1 :
    closedCollarIndexStepBool word fiber50 13 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_13_1)
    (by decide) (by decide)
    (by simpa [cert50_move_13_1] using cert50_component_13_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_13_26 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_13_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_13_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_13_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_13_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_0 = cert50_layer_13_26_0 := by
  decide

def cert50_seen_13_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_13_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_13_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_1 = cert50_layer_13_26_1 := by
  decide

def cert50_seen_13_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_13_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_13_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_2 = cert50_layer_13_26_2 := by
  decide

def cert50_seen_13_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_13_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_13_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_3 = cert50_layer_13_26_3 := by
  decide

def cert50_seen_13_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_13_26_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_13_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_4 = cert50_layer_13_26_4 := by
  decide

def cert50_seen_13_26_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_13_26_5 : List ChainEdge :=
  []

theorem cert50_layer_13_26_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 13 [])
      LColor.r LColor.p cert50_seen_13_26_5 = cert50_layer_13_26_5 := by
  decide

theorem cert50_component_13_26_eq :
    closedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_13_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 27 cert50_seen_13_26_0 = cert50_component_13_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_0 cert50_layer_13_26_0 26 cert50_layer_13_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 26 cert50_seen_13_26_1 = cert50_component_13_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_1 cert50_layer_13_26_1 25 cert50_layer_13_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 25 cert50_seen_13_26_2 = cert50_component_13_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_2 cert50_layer_13_26_2 24 cert50_layer_13_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 24 cert50_seen_13_26_3 = cert50_component_13_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_3 cert50_layer_13_26_3 23 cert50_layer_13_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 23 cert50_seen_13_26_4 = cert50_component_13_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_4 cert50_layer_13_26_4 22 cert50_layer_13_26_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 13 [])
      LColor.r LColor.p 22 cert50_seen_13_26_5 = cert50_component_13_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 13 []) LColor.r LColor.p
    cert50_seen_13_26_5 cert50_layer_13_26_5_eq 22

theorem cert50_step_13_26 :
    closedCollarIndexStepBool word fiber50 13 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_13_26)
    (by decide) (by decide)
    (by simpa [cert50_move_13_26] using cert50_component_13_26_eq)
    (by decide) (by decide) (by decide)

def cert50_move_14_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_14_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 14 [])
      LColor.r LColor.b cert50_seen_14_2_0 = cert50_layer_14_2_0 := by
  decide

def cert50_seen_14_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_14_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_14_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 14 [])
      LColor.r LColor.b cert50_seen_14_2_1 = cert50_layer_14_2_1 := by
  decide

def cert50_seen_14_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_14_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_14_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 14 [])
      LColor.r LColor.b cert50_seen_14_2_2 = cert50_layer_14_2_2 := by
  decide

def cert50_seen_14_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_14_2_3 : List ChainEdge :=
  []

theorem cert50_layer_14_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 14 [])
      LColor.r LColor.b cert50_seen_14_2_3 = cert50_layer_14_2_3 := by
  decide

theorem cert50_component_14_2_eq :
    closedCollarComponent word (listGetD fiber50 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_14_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 14 [])
      LColor.r LColor.b 27 cert50_seen_14_2_0 = cert50_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 14 []) LColor.r LColor.b
    cert50_seen_14_2_0 cert50_layer_14_2_0 26 cert50_layer_14_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 14 [])
      LColor.r LColor.b 26 cert50_seen_14_2_1 = cert50_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 14 []) LColor.r LColor.b
    cert50_seen_14_2_1 cert50_layer_14_2_1 25 cert50_layer_14_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 14 [])
      LColor.r LColor.b 25 cert50_seen_14_2_2 = cert50_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 14 []) LColor.r LColor.b
    cert50_seen_14_2_2 cert50_layer_14_2_2 24 cert50_layer_14_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 14 [])
      LColor.r LColor.b 24 cert50_seen_14_2_3 = cert50_component_14_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 14 []) LColor.r LColor.b
    cert50_seen_14_2_3 cert50_layer_14_2_3_eq 24

theorem cert50_step_14_2 :
    closedCollarIndexStepBool word fiber50 14 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_14_2)
    (by decide) (by decide)
    (by simpa [cert50_move_14_2] using cert50_component_14_2_eq)
    (by decide) (by decide) (by decide)

def cert50_move_15_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_15_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 15 [])
      LColor.r LColor.b cert50_seen_15_3_0 = cert50_layer_15_3_0 := by
  decide

def cert50_seen_15_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_15_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_15_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 15 [])
      LColor.r LColor.b cert50_seen_15_3_1 = cert50_layer_15_3_1 := by
  decide

def cert50_seen_15_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_15_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_15_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 15 [])
      LColor.r LColor.b cert50_seen_15_3_2 = cert50_layer_15_3_2 := by
  decide

def cert50_seen_15_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_15_3_3 : List ChainEdge :=
  []

theorem cert50_layer_15_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 15 [])
      LColor.r LColor.b cert50_seen_15_3_3 = cert50_layer_15_3_3 := by
  decide

theorem cert50_component_15_3_eq :
    closedCollarComponent word (listGetD fiber50 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_15_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 15 [])
      LColor.r LColor.b 27 cert50_seen_15_3_0 = cert50_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 15 []) LColor.r LColor.b
    cert50_seen_15_3_0 cert50_layer_15_3_0 26 cert50_layer_15_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 15 [])
      LColor.r LColor.b 26 cert50_seen_15_3_1 = cert50_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 15 []) LColor.r LColor.b
    cert50_seen_15_3_1 cert50_layer_15_3_1 25 cert50_layer_15_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 15 [])
      LColor.r LColor.b 25 cert50_seen_15_3_2 = cert50_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 15 []) LColor.r LColor.b
    cert50_seen_15_3_2 cert50_layer_15_3_2 24 cert50_layer_15_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 15 [])
      LColor.r LColor.b 24 cert50_seen_15_3_3 = cert50_component_15_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 15 []) LColor.r LColor.b
    cert50_seen_15_3_3 cert50_layer_15_3_3_eq 24

theorem cert50_step_15_3 :
    closedCollarIndexStepBool word fiber50 15 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_15_3)
    (by decide) (by decide)
    (by simpa [cert50_move_15_3] using cert50_component_15_3_eq)
    (by decide) (by decide) (by decide)

def cert50_move_16_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_16_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_0 = cert50_layer_16_4_0 := by
  decide

def cert50_seen_16_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_16_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_16_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_1 = cert50_layer_16_4_1 := by
  decide

def cert50_seen_16_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_16_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_16_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_2 = cert50_layer_16_4_2 := by
  decide

def cert50_seen_16_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_16_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_16_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_3 = cert50_layer_16_4_3 := by
  decide

def cert50_seen_16_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_16_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_16_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_4 = cert50_layer_16_4_4 := by
  decide

def cert50_seen_16_4_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_16_4_5 : List ChainEdge :=
  []

theorem cert50_layer_16_4_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.b cert50_seen_16_4_5 = cert50_layer_16_4_5 := by
  decide

theorem cert50_component_16_4_eq :
    closedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_16_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 27 cert50_seen_16_4_0 = cert50_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_0 cert50_layer_16_4_0 26 cert50_layer_16_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 26 cert50_seen_16_4_1 = cert50_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_1 cert50_layer_16_4_1 25 cert50_layer_16_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 25 cert50_seen_16_4_2 = cert50_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_2 cert50_layer_16_4_2 24 cert50_layer_16_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 24 cert50_seen_16_4_3 = cert50_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_3 cert50_layer_16_4_3 23 cert50_layer_16_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 23 cert50_seen_16_4_4 = cert50_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_4 cert50_layer_16_4_4 22 cert50_layer_16_4_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.b 22 cert50_seen_16_4_5 = cert50_component_16_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 16 []) LColor.r LColor.b
    cert50_seen_16_4_5 cert50_layer_16_4_5_eq 22

theorem cert50_step_16_4 :
    closedCollarIndexStepBool word fiber50 16 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_16_4)
    (by decide) (by decide)
    (by simpa [cert50_move_16_4] using cert50_component_16_4_eq)
    (by decide) (by decide) (by decide)

def cert50_move_16_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_16_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_seen_16_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_16_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_16_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.p cert50_seen_16_24_0 = cert50_layer_16_24_0 := by
  decide

def cert50_seen_16_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_16_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_16_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.p cert50_seen_16_24_1 = cert50_layer_16_24_1 := by
  decide

def cert50_seen_16_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_16_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_16_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.p cert50_seen_16_24_2 = cert50_layer_16_24_2 := by
  decide

def cert50_seen_16_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_16_24_3 : List ChainEdge :=
  []

theorem cert50_layer_16_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 16 [])
      LColor.r LColor.p cert50_seen_16_24_3 = cert50_layer_16_24_3 := by
  decide

theorem cert50_component_16_24_eq :
    closedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_16_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.p 27 cert50_seen_16_24_0 = cert50_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.p
    cert50_seen_16_24_0 cert50_layer_16_24_0 26 cert50_layer_16_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.p 26 cert50_seen_16_24_1 = cert50_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.p
    cert50_seen_16_24_1 cert50_layer_16_24_1 25 cert50_layer_16_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.p 25 cert50_seen_16_24_2 = cert50_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 16 []) LColor.r LColor.p
    cert50_seen_16_24_2 cert50_layer_16_24_2 24 cert50_layer_16_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 16 [])
      LColor.r LColor.p 24 cert50_seen_16_24_3 = cert50_component_16_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 16 []) LColor.r LColor.p
    cert50_seen_16_24_3 cert50_layer_16_24_3_eq 24

theorem cert50_step_16_24 :
    closedCollarIndexStepBool word fiber50 16 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_16_24)
    (by decide) (by decide)
    (by simpa [cert50_move_16_24] using cert50_component_16_24_eq)
    (by decide) (by decide) (by decide)

def cert50_move_17_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_17_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_0 = cert50_layer_17_5_0 := by
  decide

def cert50_seen_17_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_17_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_17_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_1 = cert50_layer_17_5_1 := by
  decide

def cert50_seen_17_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_17_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_17_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_2 = cert50_layer_17_5_2 := by
  decide

def cert50_seen_17_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_17_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_17_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_3 = cert50_layer_17_5_3 := by
  decide

def cert50_seen_17_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_17_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_17_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_4 = cert50_layer_17_5_4 := by
  decide

def cert50_seen_17_5_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_17_5_5 : List ChainEdge :=
  []

theorem cert50_layer_17_5_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.b cert50_seen_17_5_5 = cert50_layer_17_5_5 := by
  decide

theorem cert50_component_17_5_eq :
    closedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_17_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 27 cert50_seen_17_5_0 = cert50_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_0 cert50_layer_17_5_0 26 cert50_layer_17_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 26 cert50_seen_17_5_1 = cert50_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_1 cert50_layer_17_5_1 25 cert50_layer_17_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 25 cert50_seen_17_5_2 = cert50_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_2 cert50_layer_17_5_2 24 cert50_layer_17_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 24 cert50_seen_17_5_3 = cert50_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_3 cert50_layer_17_5_3 23 cert50_layer_17_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 23 cert50_seen_17_5_4 = cert50_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_4 cert50_layer_17_5_4 22 cert50_layer_17_5_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.b 22 cert50_seen_17_5_5 = cert50_component_17_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 17 []) LColor.r LColor.b
    cert50_seen_17_5_5 cert50_layer_17_5_5_eq 22

theorem cert50_step_17_5 :
    closedCollarIndexStepBool word fiber50 17 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_17_5)
    (by decide) (by decide)
    (by simpa [cert50_move_17_5] using cert50_component_17_5_eq)
    (by decide) (by decide) (by decide)

def cert50_move_17_25 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_17_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_seen_17_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_17_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_17_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.p cert50_seen_17_25_0 = cert50_layer_17_25_0 := by
  decide

def cert50_seen_17_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_17_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_17_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.p cert50_seen_17_25_1 = cert50_layer_17_25_1 := by
  decide

def cert50_seen_17_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_17_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_17_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.p cert50_seen_17_25_2 = cert50_layer_17_25_2 := by
  decide

def cert50_seen_17_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_17_25_3 : List ChainEdge :=
  []

theorem cert50_layer_17_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 17 [])
      LColor.r LColor.p cert50_seen_17_25_3 = cert50_layer_17_25_3 := by
  decide

theorem cert50_component_17_25_eq :
    closedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_17_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.p 27 cert50_seen_17_25_0 = cert50_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.p
    cert50_seen_17_25_0 cert50_layer_17_25_0 26 cert50_layer_17_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.p 26 cert50_seen_17_25_1 = cert50_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.p
    cert50_seen_17_25_1 cert50_layer_17_25_1 25 cert50_layer_17_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.p 25 cert50_seen_17_25_2 = cert50_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 17 []) LColor.r LColor.p
    cert50_seen_17_25_2 cert50_layer_17_25_2 24 cert50_layer_17_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 17 [])
      LColor.r LColor.p 24 cert50_seen_17_25_3 = cert50_component_17_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 17 []) LColor.r LColor.p
    cert50_seen_17_25_3 cert50_layer_17_25_3_eq 24

theorem cert50_step_17_25 :
    closedCollarIndexStepBool word fiber50 17 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_17_25)
    (by decide) (by decide)
    (by simpa [cert50_move_17_25] using cert50_component_17_25_eq)
    (by decide) (by decide) (by decide)

def cert50_move_18_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_18_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_18_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 18 [])
      LColor.r LColor.b cert50_seen_18_6_0 = cert50_layer_18_6_0 := by
  decide

def cert50_seen_18_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_18_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_18_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 18 [])
      LColor.r LColor.b cert50_seen_18_6_1 = cert50_layer_18_6_1 := by
  decide

def cert50_seen_18_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_18_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_18_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 18 [])
      LColor.r LColor.b cert50_seen_18_6_2 = cert50_layer_18_6_2 := by
  decide

def cert50_seen_18_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_18_6_3 : List ChainEdge :=
  []

theorem cert50_layer_18_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 18 [])
      LColor.r LColor.b cert50_seen_18_6_3 = cert50_layer_18_6_3 := by
  decide

theorem cert50_component_18_6_eq :
    closedCollarComponent word (listGetD fiber50 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_18_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 18 [])
      LColor.r LColor.b 27 cert50_seen_18_6_0 = cert50_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 18 []) LColor.r LColor.b
    cert50_seen_18_6_0 cert50_layer_18_6_0 26 cert50_layer_18_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 18 [])
      LColor.r LColor.b 26 cert50_seen_18_6_1 = cert50_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 18 []) LColor.r LColor.b
    cert50_seen_18_6_1 cert50_layer_18_6_1 25 cert50_layer_18_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 18 [])
      LColor.r LColor.b 25 cert50_seen_18_6_2 = cert50_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 18 []) LColor.r LColor.b
    cert50_seen_18_6_2 cert50_layer_18_6_2 24 cert50_layer_18_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 18 [])
      LColor.r LColor.b 24 cert50_seen_18_6_3 = cert50_component_18_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 18 []) LColor.r LColor.b
    cert50_seen_18_6_3 cert50_layer_18_6_3_eq 24

theorem cert50_step_18_6 :
    closedCollarIndexStepBool word fiber50 18 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_18_6)
    (by decide) (by decide)
    (by simpa [cert50_move_18_6] using cert50_component_18_6_eq)
    (by decide) (by decide) (by decide)

def cert50_move_19_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_19_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_19_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 19 [])
      LColor.r LColor.b cert50_seen_19_7_0 = cert50_layer_19_7_0 := by
  decide

def cert50_seen_19_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_19_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_19_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 19 [])
      LColor.r LColor.b cert50_seen_19_7_1 = cert50_layer_19_7_1 := by
  decide

def cert50_seen_19_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_19_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_19_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 19 [])
      LColor.r LColor.b cert50_seen_19_7_2 = cert50_layer_19_7_2 := by
  decide

def cert50_seen_19_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_19_7_3 : List ChainEdge :=
  []

theorem cert50_layer_19_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 19 [])
      LColor.r LColor.b cert50_seen_19_7_3 = cert50_layer_19_7_3 := by
  decide

theorem cert50_component_19_7_eq :
    closedCollarComponent word (listGetD fiber50 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_19_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 19 [])
      LColor.r LColor.b 27 cert50_seen_19_7_0 = cert50_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 19 []) LColor.r LColor.b
    cert50_seen_19_7_0 cert50_layer_19_7_0 26 cert50_layer_19_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 19 [])
      LColor.r LColor.b 26 cert50_seen_19_7_1 = cert50_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 19 []) LColor.r LColor.b
    cert50_seen_19_7_1 cert50_layer_19_7_1 25 cert50_layer_19_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 19 [])
      LColor.r LColor.b 25 cert50_seen_19_7_2 = cert50_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 19 []) LColor.r LColor.b
    cert50_seen_19_7_2 cert50_layer_19_7_2 24 cert50_layer_19_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 19 [])
      LColor.r LColor.b 24 cert50_seen_19_7_3 = cert50_component_19_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 19 []) LColor.r LColor.b
    cert50_seen_19_7_3 cert50_layer_19_7_3_eq 24

theorem cert50_step_19_7 :
    closedCollarIndexStepBool word fiber50 19 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_19_7)
    (by decide) (by decide)
    (by simpa [cert50_move_19_7] using cert50_component_19_7_eq)
    (by decide) (by decide) (by decide)

def cert50_move_20_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_20_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_20_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 20 [])
      LColor.r LColor.b cert50_seen_20_8_0 = cert50_layer_20_8_0 := by
  decide

def cert50_seen_20_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_20_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_20_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 20 [])
      LColor.r LColor.b cert50_seen_20_8_1 = cert50_layer_20_8_1 := by
  decide

def cert50_seen_20_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_20_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_20_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 20 [])
      LColor.r LColor.b cert50_seen_20_8_2 = cert50_layer_20_8_2 := by
  decide

def cert50_seen_20_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_20_8_3 : List ChainEdge :=
  []

theorem cert50_layer_20_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 20 [])
      LColor.r LColor.b cert50_seen_20_8_3 = cert50_layer_20_8_3 := by
  decide

theorem cert50_component_20_8_eq :
    closedCollarComponent word (listGetD fiber50 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_20_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 20 [])
      LColor.r LColor.b 27 cert50_seen_20_8_0 = cert50_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 20 []) LColor.r LColor.b
    cert50_seen_20_8_0 cert50_layer_20_8_0 26 cert50_layer_20_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 20 [])
      LColor.r LColor.b 26 cert50_seen_20_8_1 = cert50_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 20 []) LColor.r LColor.b
    cert50_seen_20_8_1 cert50_layer_20_8_1 25 cert50_layer_20_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 20 [])
      LColor.r LColor.b 25 cert50_seen_20_8_2 = cert50_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 20 []) LColor.r LColor.b
    cert50_seen_20_8_2 cert50_layer_20_8_2 24 cert50_layer_20_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 20 [])
      LColor.r LColor.b 24 cert50_seen_20_8_3 = cert50_component_20_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 20 []) LColor.r LColor.b
    cert50_seen_20_8_3 cert50_layer_20_8_3_eq 24

theorem cert50_step_20_8 :
    closedCollarIndexStepBool word fiber50 20 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_20_8)
    (by decide) (by decide)
    (by simpa [cert50_move_20_8] using cert50_component_20_8_eq)
    (by decide) (by decide) (by decide)

def cert50_move_21_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_21_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_21_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 21 [])
      LColor.r LColor.b cert50_seen_21_9_0 = cert50_layer_21_9_0 := by
  decide

def cert50_seen_21_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_21_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_21_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 21 [])
      LColor.r LColor.b cert50_seen_21_9_1 = cert50_layer_21_9_1 := by
  decide

def cert50_seen_21_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_21_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_21_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 21 [])
      LColor.r LColor.b cert50_seen_21_9_2 = cert50_layer_21_9_2 := by
  decide

def cert50_seen_21_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_21_9_3 : List ChainEdge :=
  []

theorem cert50_layer_21_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 21 [])
      LColor.r LColor.b cert50_seen_21_9_3 = cert50_layer_21_9_3 := by
  decide

theorem cert50_component_21_9_eq :
    closedCollarComponent word (listGetD fiber50 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_21_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 21 [])
      LColor.r LColor.b 27 cert50_seen_21_9_0 = cert50_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 21 []) LColor.r LColor.b
    cert50_seen_21_9_0 cert50_layer_21_9_0 26 cert50_layer_21_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 21 [])
      LColor.r LColor.b 26 cert50_seen_21_9_1 = cert50_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 21 []) LColor.r LColor.b
    cert50_seen_21_9_1 cert50_layer_21_9_1 25 cert50_layer_21_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 21 [])
      LColor.r LColor.b 25 cert50_seen_21_9_2 = cert50_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 21 []) LColor.r LColor.b
    cert50_seen_21_9_2 cert50_layer_21_9_2 24 cert50_layer_21_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 21 [])
      LColor.r LColor.b 24 cert50_seen_21_9_3 = cert50_component_21_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 21 []) LColor.r LColor.b
    cert50_seen_21_9_3 cert50_layer_21_9_3_eq 24

theorem cert50_step_21_9 :
    closedCollarIndexStepBool word fiber50 21 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_21_9)
    (by decide) (by decide)
    (by simpa [cert50_move_21_9] using cert50_component_21_9_eq)
    (by decide) (by decide) (by decide)

def cert50_move_22_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_22_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_22_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_0 = cert50_layer_22_10_0 := by
  decide

def cert50_seen_22_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_22_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_22_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_1 = cert50_layer_22_10_1 := by
  decide

def cert50_seen_22_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_22_10_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_22_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_2 = cert50_layer_22_10_2 := by
  decide

def cert50_seen_22_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_22_10_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_22_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_3 = cert50_layer_22_10_3 := by
  decide

def cert50_seen_22_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_22_10_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_22_10_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_4 = cert50_layer_22_10_4 := by
  decide

def cert50_seen_22_10_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_22_10_5 : List ChainEdge :=
  []

theorem cert50_layer_22_10_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 22 [])
      LColor.r LColor.b cert50_seen_22_10_5 = cert50_layer_22_10_5 := by
  decide

theorem cert50_component_22_10_eq :
    closedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_22_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 27 cert50_seen_22_10_0 = cert50_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_0 cert50_layer_22_10_0 26 cert50_layer_22_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 26 cert50_seen_22_10_1 = cert50_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_1 cert50_layer_22_10_1 25 cert50_layer_22_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 25 cert50_seen_22_10_2 = cert50_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_2 cert50_layer_22_10_2 24 cert50_layer_22_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 24 cert50_seen_22_10_3 = cert50_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_3 cert50_layer_22_10_3 23 cert50_layer_22_10_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 23 cert50_seen_22_10_4 = cert50_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_4 cert50_layer_22_10_4 22 cert50_layer_22_10_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 22 [])
      LColor.r LColor.b 22 cert50_seen_22_10_5 = cert50_component_22_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 22 []) LColor.r LColor.b
    cert50_seen_22_10_5 cert50_layer_22_10_5_eq 22

theorem cert50_step_22_10 :
    closedCollarIndexStepBool word fiber50 22 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_22_10)
    (by decide) (by decide)
    (by simpa [cert50_move_22_10] using cert50_component_22_10_eq)
    (by decide) (by decide) (by decide)

def cert50_move_23_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_23_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_seen_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_23_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_0 = cert50_layer_23_11_0 := by
  decide

def cert50_seen_23_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_23_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_23_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_1 = cert50_layer_23_11_1 := by
  decide

def cert50_seen_23_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_23_11_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert50_layer_23_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_2 = cert50_layer_23_11_2 := by
  decide

def cert50_seen_23_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert50_layer_23_11_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert50_layer_23_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_3 = cert50_layer_23_11_3 := by
  decide

def cert50_seen_23_11_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert50_layer_23_11_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert50_layer_23_11_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_4 = cert50_layer_23_11_4 := by
  decide

def cert50_seen_23_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert50_layer_23_11_5 : List ChainEdge :=
  []

theorem cert50_layer_23_11_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 23 [])
      LColor.r LColor.b cert50_seen_23_11_5 = cert50_layer_23_11_5 := by
  decide

theorem cert50_component_23_11_eq :
    closedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert50_component_23_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 27 cert50_seen_23_11_0 = cert50_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_0 cert50_layer_23_11_0 26 cert50_layer_23_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 26 cert50_seen_23_11_1 = cert50_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_1 cert50_layer_23_11_1 25 cert50_layer_23_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 25 cert50_seen_23_11_2 = cert50_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_2 cert50_layer_23_11_2 24 cert50_layer_23_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 24 cert50_seen_23_11_3 = cert50_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_3 cert50_layer_23_11_3 23 cert50_layer_23_11_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 23 cert50_seen_23_11_4 = cert50_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_4 cert50_layer_23_11_4 22 cert50_layer_23_11_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 23 [])
      LColor.r LColor.b 22 cert50_seen_23_11_5 = cert50_component_23_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 23 []) LColor.r LColor.b
    cert50_seen_23_11_5 cert50_layer_23_11_5_eq 22

theorem cert50_step_23_11 :
    closedCollarIndexStepBool word fiber50 23 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_23_11)
    (by decide) (by decide)
    (by simpa [cert50_move_23_11] using cert50_component_23_11_eq)
    (by decide) (by decide) (by decide)

def cert50_move_24_16 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_24_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_seen_24_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_24_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_24_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 24 [])
      LColor.r LColor.p cert50_seen_24_16_0 = cert50_layer_24_16_0 := by
  decide

def cert50_seen_24_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_24_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_24_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 24 [])
      LColor.r LColor.p cert50_seen_24_16_1 = cert50_layer_24_16_1 := by
  decide

def cert50_seen_24_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_24_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_24_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 24 [])
      LColor.r LColor.p cert50_seen_24_16_2 = cert50_layer_24_16_2 := by
  decide

def cert50_seen_24_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_24_16_3 : List ChainEdge :=
  []

theorem cert50_layer_24_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 24 [])
      LColor.r LColor.p cert50_seen_24_16_3 = cert50_layer_24_16_3 := by
  decide

theorem cert50_component_24_16_eq :
    closedCollarComponent word (listGetD fiber50 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_24_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 24 [])
      LColor.r LColor.p 27 cert50_seen_24_16_0 = cert50_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 24 []) LColor.r LColor.p
    cert50_seen_24_16_0 cert50_layer_24_16_0 26 cert50_layer_24_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 24 [])
      LColor.r LColor.p 26 cert50_seen_24_16_1 = cert50_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 24 []) LColor.r LColor.p
    cert50_seen_24_16_1 cert50_layer_24_16_1 25 cert50_layer_24_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 24 [])
      LColor.r LColor.p 25 cert50_seen_24_16_2 = cert50_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 24 []) LColor.r LColor.p
    cert50_seen_24_16_2 cert50_layer_24_16_2 24 cert50_layer_24_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 24 [])
      LColor.r LColor.p 24 cert50_seen_24_16_3 = cert50_component_24_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 24 []) LColor.r LColor.p
    cert50_seen_24_16_3 cert50_layer_24_16_3_eq 24

theorem cert50_step_24_16 :
    closedCollarIndexStepBool word fiber50 24 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_24_16)
    (by decide) (by decide)
    (by simpa [cert50_move_24_16] using cert50_component_24_16_eq)
    (by decide) (by decide) (by decide)

def cert50_move_25_17 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_25_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_seen_25_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_25_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_25_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 25 [])
      LColor.r LColor.p cert50_seen_25_17_0 = cert50_layer_25_17_0 := by
  decide

def cert50_seen_25_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_25_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_25_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 25 [])
      LColor.r LColor.p cert50_seen_25_17_1 = cert50_layer_25_17_1 := by
  decide

def cert50_seen_25_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_25_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_25_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 25 [])
      LColor.r LColor.p cert50_seen_25_17_2 = cert50_layer_25_17_2 := by
  decide

def cert50_seen_25_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_25_17_3 : List ChainEdge :=
  []

theorem cert50_layer_25_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 25 [])
      LColor.r LColor.p cert50_seen_25_17_3 = cert50_layer_25_17_3 := by
  decide

theorem cert50_component_25_17_eq :
    closedCollarComponent word (listGetD fiber50 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_25_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 25 [])
      LColor.r LColor.p 27 cert50_seen_25_17_0 = cert50_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 25 []) LColor.r LColor.p
    cert50_seen_25_17_0 cert50_layer_25_17_0 26 cert50_layer_25_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 25 [])
      LColor.r LColor.p 26 cert50_seen_25_17_1 = cert50_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 25 []) LColor.r LColor.p
    cert50_seen_25_17_1 cert50_layer_25_17_1 25 cert50_layer_25_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 25 [])
      LColor.r LColor.p 25 cert50_seen_25_17_2 = cert50_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 25 []) LColor.r LColor.p
    cert50_seen_25_17_2 cert50_layer_25_17_2 24 cert50_layer_25_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 25 [])
      LColor.r LColor.p 24 cert50_seen_25_17_3 = cert50_component_25_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 25 []) LColor.r LColor.p
    cert50_seen_25_17_3 cert50_layer_25_17_3_eq 24

theorem cert50_step_25_17 :
    closedCollarIndexStepBool word fiber50 25 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_25_17)
    (by decide) (by decide)
    (by simpa [cert50_move_25_17] using cert50_component_25_17_eq)
    (by decide) (by decide) (by decide)

def cert50_move_26_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_26_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_seen_26_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_26_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_26_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_0 = cert50_layer_26_13_0 := by
  decide

def cert50_seen_26_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_26_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_26_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_1 = cert50_layer_26_13_1 := by
  decide

def cert50_seen_26_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_26_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_26_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_2 = cert50_layer_26_13_2 := by
  decide

def cert50_seen_26_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_26_13_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_26_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_3 = cert50_layer_26_13_3 := by
  decide

def cert50_seen_26_13_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_26_13_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_26_13_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_4 = cert50_layer_26_13_4 := by
  decide

def cert50_seen_26_13_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_26_13_5 : List ChainEdge :=
  []

theorem cert50_layer_26_13_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 26 [])
      LColor.r LColor.p cert50_seen_26_13_5 = cert50_layer_26_13_5 := by
  decide

theorem cert50_component_26_13_eq :
    closedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_26_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 27 cert50_seen_26_13_0 = cert50_component_26_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_0 cert50_layer_26_13_0 26 cert50_layer_26_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 26 cert50_seen_26_13_1 = cert50_component_26_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_1 cert50_layer_26_13_1 25 cert50_layer_26_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 25 cert50_seen_26_13_2 = cert50_component_26_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_2 cert50_layer_26_13_2 24 cert50_layer_26_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 24 cert50_seen_26_13_3 = cert50_component_26_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_3 cert50_layer_26_13_3 23 cert50_layer_26_13_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 23 cert50_seen_26_13_4 = cert50_component_26_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_4 cert50_layer_26_13_4 22 cert50_layer_26_13_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 26 [])
      LColor.r LColor.p 22 cert50_seen_26_13_5 = cert50_component_26_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 26 []) LColor.r LColor.p
    cert50_seen_26_13_5 cert50_layer_26_13_5_eq 22

theorem cert50_step_26_13 :
    closedCollarIndexStepBool word fiber50 26 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_26_13)
    (by decide) (by decide)
    (by simpa [cert50_move_26_13] using cert50_component_26_13_eq)
    (by decide) (by decide) (by decide)

def cert50_move_27_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_27_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_seen_27_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_27_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_27_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_0 = cert50_layer_27_12_0 := by
  decide

def cert50_seen_27_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_27_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_27_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_1 = cert50_layer_27_12_1 := by
  decide

def cert50_seen_27_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_27_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_27_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_2 = cert50_layer_27_12_2 := by
  decide

def cert50_seen_27_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_27_12_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_27_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_3 = cert50_layer_27_12_3 := by
  decide

def cert50_seen_27_12_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_27_12_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_27_12_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_4 = cert50_layer_27_12_4 := by
  decide

def cert50_seen_27_12_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_27_12_5 : List ChainEdge :=
  []

theorem cert50_layer_27_12_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 27 [])
      LColor.r LColor.p cert50_seen_27_12_5 = cert50_layer_27_12_5 := by
  decide

theorem cert50_component_27_12_eq :
    closedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_27_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 27 cert50_seen_27_12_0 = cert50_component_27_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_0 cert50_layer_27_12_0 26 cert50_layer_27_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 26 cert50_seen_27_12_1 = cert50_component_27_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_1 cert50_layer_27_12_1 25 cert50_layer_27_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 25 cert50_seen_27_12_2 = cert50_component_27_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_2 cert50_layer_27_12_2 24 cert50_layer_27_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 24 cert50_seen_27_12_3 = cert50_component_27_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_3 cert50_layer_27_12_3 23 cert50_layer_27_12_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 23 cert50_seen_27_12_4 = cert50_component_27_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_4 cert50_layer_27_12_4 22 cert50_layer_27_12_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 27 [])
      LColor.r LColor.p 22 cert50_seen_27_12_5 = cert50_component_27_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 27 []) LColor.r LColor.p
    cert50_seen_27_12_5 cert50_layer_27_12_5_eq 22

theorem cert50_step_27_12 :
    closedCollarIndexStepBool word fiber50 27 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_27_12)
    (by decide) (by decide)
    (by simpa [cert50_move_27_12] using cert50_component_27_12_eq)
    (by decide) (by decide) (by decide)

def cert50_move_28_40 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_28_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_seen_28_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_28_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_28_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_0 = cert50_layer_28_40_0 := by
  decide

def cert50_seen_28_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_28_40_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_28_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_1 = cert50_layer_28_40_1 := by
  decide

def cert50_seen_28_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_28_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_28_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_2 = cert50_layer_28_40_2 := by
  decide

def cert50_seen_28_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_28_40_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_28_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_3 = cert50_layer_28_40_3 := by
  decide

def cert50_seen_28_40_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_28_40_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert50_layer_28_40_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_4 = cert50_layer_28_40_4 := by
  decide

def cert50_seen_28_40_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_28_40_5 : List ChainEdge :=
  []

theorem cert50_layer_28_40_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 28 [])
      LColor.b LColor.p cert50_seen_28_40_5 = cert50_layer_28_40_5 := by
  decide

theorem cert50_component_28_40_eq :
    closedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_28_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 27 cert50_seen_28_40_0 = cert50_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_0 cert50_layer_28_40_0 26 cert50_layer_28_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 26 cert50_seen_28_40_1 = cert50_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_1 cert50_layer_28_40_1 25 cert50_layer_28_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 25 cert50_seen_28_40_2 = cert50_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_2 cert50_layer_28_40_2 24 cert50_layer_28_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 24 cert50_seen_28_40_3 = cert50_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_3 cert50_layer_28_40_3 23 cert50_layer_28_40_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 23 cert50_seen_28_40_4 = cert50_component_28_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_4 cert50_layer_28_40_4 22 cert50_layer_28_40_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 28 [])
      LColor.b LColor.p 22 cert50_seen_28_40_5 = cert50_component_28_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 28 []) LColor.b LColor.p
    cert50_seen_28_40_5 cert50_layer_28_40_5_eq 22

theorem cert50_step_28_40 :
    closedCollarIndexStepBool word fiber50 28 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_28_40)
    (by decide) (by decide)
    (by simpa [cert50_move_28_40] using cert50_component_28_40_eq)
    (by decide) (by decide) (by decide)

def cert50_move_29_41 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_29_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_seen_29_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_29_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_29_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_0 = cert50_layer_29_41_0 := by
  decide

def cert50_seen_29_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_29_41_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_29_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_1 = cert50_layer_29_41_1 := by
  decide

def cert50_seen_29_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_29_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_29_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_2 = cert50_layer_29_41_2 := by
  decide

def cert50_seen_29_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_29_41_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_29_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_3 = cert50_layer_29_41_3 := by
  decide

def cert50_seen_29_41_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_29_41_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert50_layer_29_41_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_4 = cert50_layer_29_41_4 := by
  decide

def cert50_seen_29_41_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_29_41_5 : List ChainEdge :=
  []

theorem cert50_layer_29_41_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 29 [])
      LColor.b LColor.p cert50_seen_29_41_5 = cert50_layer_29_41_5 := by
  decide

theorem cert50_component_29_41_eq :
    closedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_29_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 27 cert50_seen_29_41_0 = cert50_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_0 cert50_layer_29_41_0 26 cert50_layer_29_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 26 cert50_seen_29_41_1 = cert50_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_1 cert50_layer_29_41_1 25 cert50_layer_29_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 25 cert50_seen_29_41_2 = cert50_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_2 cert50_layer_29_41_2 24 cert50_layer_29_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 24 cert50_seen_29_41_3 = cert50_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_3 cert50_layer_29_41_3 23 cert50_layer_29_41_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 23 cert50_seen_29_41_4 = cert50_component_29_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_4 cert50_layer_29_41_4 22 cert50_layer_29_41_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 29 [])
      LColor.b LColor.p 22 cert50_seen_29_41_5 = cert50_component_29_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 29 []) LColor.b LColor.p
    cert50_seen_29_41_5 cert50_layer_29_41_5_eq 22

theorem cert50_step_29_41 :
    closedCollarIndexStepBool word fiber50 29 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_29_41)
    (by decide) (by decide)
    (by simpa [cert50_move_29_41] using cert50_component_29_41_eq)
    (by decide) (by decide) (by decide)

def cert50_move_30_42 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_30_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_30_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_30_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_30_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 30 [])
      LColor.b LColor.p cert50_seen_30_42_0 = cert50_layer_30_42_0 := by
  decide

def cert50_seen_30_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_30_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_30_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 30 [])
      LColor.b LColor.p cert50_seen_30_42_1 = cert50_layer_30_42_1 := by
  decide

def cert50_seen_30_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_30_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_30_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 30 [])
      LColor.b LColor.p cert50_seen_30_42_2 = cert50_layer_30_42_2 := by
  decide

def cert50_seen_30_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_30_42_3 : List ChainEdge :=
  []

theorem cert50_layer_30_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 30 [])
      LColor.b LColor.p cert50_seen_30_42_3 = cert50_layer_30_42_3 := by
  decide

theorem cert50_component_30_42_eq :
    closedCollarComponent word (listGetD fiber50 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_30_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 30 [])
      LColor.b LColor.p 27 cert50_seen_30_42_0 = cert50_component_30_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 30 []) LColor.b LColor.p
    cert50_seen_30_42_0 cert50_layer_30_42_0 26 cert50_layer_30_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 30 [])
      LColor.b LColor.p 26 cert50_seen_30_42_1 = cert50_component_30_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 30 []) LColor.b LColor.p
    cert50_seen_30_42_1 cert50_layer_30_42_1 25 cert50_layer_30_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 30 [])
      LColor.b LColor.p 25 cert50_seen_30_42_2 = cert50_component_30_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 30 []) LColor.b LColor.p
    cert50_seen_30_42_2 cert50_layer_30_42_2 24 cert50_layer_30_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 30 [])
      LColor.b LColor.p 24 cert50_seen_30_42_3 = cert50_component_30_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 30 []) LColor.b LColor.p
    cert50_seen_30_42_3 cert50_layer_30_42_3_eq 24

theorem cert50_step_30_42 :
    closedCollarIndexStepBool word fiber50 30 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_30_42)
    (by decide) (by decide)
    (by simpa [cert50_move_30_42] using cert50_component_30_42_eq)
    (by decide) (by decide) (by decide)

def cert50_move_31_43 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_31_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_31_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_31_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_31_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 31 [])
      LColor.b LColor.p cert50_seen_31_43_0 = cert50_layer_31_43_0 := by
  decide

def cert50_seen_31_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_31_43_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_31_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 31 [])
      LColor.b LColor.p cert50_seen_31_43_1 = cert50_layer_31_43_1 := by
  decide

def cert50_seen_31_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_31_43_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_31_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 31 [])
      LColor.b LColor.p cert50_seen_31_43_2 = cert50_layer_31_43_2 := by
  decide

def cert50_seen_31_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_31_43_3 : List ChainEdge :=
  []

theorem cert50_layer_31_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 31 [])
      LColor.b LColor.p cert50_seen_31_43_3 = cert50_layer_31_43_3 := by
  decide

theorem cert50_component_31_43_eq :
    closedCollarComponent word (listGetD fiber50 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_31_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 31 [])
      LColor.b LColor.p 27 cert50_seen_31_43_0 = cert50_component_31_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 31 []) LColor.b LColor.p
    cert50_seen_31_43_0 cert50_layer_31_43_0 26 cert50_layer_31_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 31 [])
      LColor.b LColor.p 26 cert50_seen_31_43_1 = cert50_component_31_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 31 []) LColor.b LColor.p
    cert50_seen_31_43_1 cert50_layer_31_43_1 25 cert50_layer_31_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 31 [])
      LColor.b LColor.p 25 cert50_seen_31_43_2 = cert50_component_31_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 31 []) LColor.b LColor.p
    cert50_seen_31_43_2 cert50_layer_31_43_2 24 cert50_layer_31_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 31 [])
      LColor.b LColor.p 24 cert50_seen_31_43_3 = cert50_component_31_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 31 []) LColor.b LColor.p
    cert50_seen_31_43_3 cert50_layer_31_43_3_eq 24

theorem cert50_step_31_43 :
    closedCollarIndexStepBool word fiber50 31 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_31_43)
    (by decide) (by decide)
    (by simpa [cert50_move_31_43] using cert50_component_31_43_eq)
    (by decide) (by decide) (by decide)

def cert50_move_32_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_32_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_32_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_32_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_32_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 32 [])
      LColor.r LColor.p cert50_seen_32_6_0 = cert50_layer_32_6_0 := by
  decide

def cert50_seen_32_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_32_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_32_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 32 [])
      LColor.r LColor.p cert50_seen_32_6_1 = cert50_layer_32_6_1 := by
  decide

def cert50_seen_32_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_32_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_32_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 32 [])
      LColor.r LColor.p cert50_seen_32_6_2 = cert50_layer_32_6_2 := by
  decide

def cert50_seen_32_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_32_6_3 : List ChainEdge :=
  []

theorem cert50_layer_32_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 32 [])
      LColor.r LColor.p cert50_seen_32_6_3 = cert50_layer_32_6_3 := by
  decide

theorem cert50_component_32_6_eq :
    closedCollarComponent word (listGetD fiber50 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_32_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 32 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 32 [])
      LColor.r LColor.p 27 cert50_seen_32_6_0 = cert50_component_32_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 32 []) LColor.r LColor.p
    cert50_seen_32_6_0 cert50_layer_32_6_0 26 cert50_layer_32_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 32 [])
      LColor.r LColor.p 26 cert50_seen_32_6_1 = cert50_component_32_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 32 []) LColor.r LColor.p
    cert50_seen_32_6_1 cert50_layer_32_6_1 25 cert50_layer_32_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 32 [])
      LColor.r LColor.p 25 cert50_seen_32_6_2 = cert50_component_32_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 32 []) LColor.r LColor.p
    cert50_seen_32_6_2 cert50_layer_32_6_2 24 cert50_layer_32_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 32 [])
      LColor.r LColor.p 24 cert50_seen_32_6_3 = cert50_component_32_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 32 []) LColor.r LColor.p
    cert50_seen_32_6_3 cert50_layer_32_6_3_eq 24

theorem cert50_step_32_6 :
    closedCollarIndexStepBool word fiber50 32 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_32_6)
    (by decide) (by decide)
    (by simpa [cert50_move_32_6] using cert50_component_32_6_eq)
    (by decide) (by decide) (by decide)

def cert50_move_33_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_33_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_33_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_33_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_33_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 33 [])
      LColor.r LColor.p cert50_seen_33_7_0 = cert50_layer_33_7_0 := by
  decide

def cert50_seen_33_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_33_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_33_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 33 [])
      LColor.r LColor.p cert50_seen_33_7_1 = cert50_layer_33_7_1 := by
  decide

def cert50_seen_33_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_33_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_33_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 33 [])
      LColor.r LColor.p cert50_seen_33_7_2 = cert50_layer_33_7_2 := by
  decide

def cert50_seen_33_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_33_7_3 : List ChainEdge :=
  []

theorem cert50_layer_33_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 33 [])
      LColor.r LColor.p cert50_seen_33_7_3 = cert50_layer_33_7_3 := by
  decide

theorem cert50_component_33_7_eq :
    closedCollarComponent word (listGetD fiber50 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_33_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 33 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 33 [])
      LColor.r LColor.p 27 cert50_seen_33_7_0 = cert50_component_33_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 33 []) LColor.r LColor.p
    cert50_seen_33_7_0 cert50_layer_33_7_0 26 cert50_layer_33_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 33 [])
      LColor.r LColor.p 26 cert50_seen_33_7_1 = cert50_component_33_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 33 []) LColor.r LColor.p
    cert50_seen_33_7_1 cert50_layer_33_7_1 25 cert50_layer_33_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 33 [])
      LColor.r LColor.p 25 cert50_seen_33_7_2 = cert50_component_33_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 33 []) LColor.r LColor.p
    cert50_seen_33_7_2 cert50_layer_33_7_2 24 cert50_layer_33_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 33 [])
      LColor.r LColor.p 24 cert50_seen_33_7_3 = cert50_component_33_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 33 []) LColor.r LColor.p
    cert50_seen_33_7_3 cert50_layer_33_7_3_eq 24

theorem cert50_step_33_7 :
    closedCollarIndexStepBool word fiber50 33 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_33_7)
    (by decide) (by decide)
    (by simpa [cert50_move_33_7] using cert50_component_33_7_eq)
    (by decide) (by decide) (by decide)

def cert50_move_34_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_34_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_34_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_34_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_34_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 34 [])
      LColor.r LColor.p cert50_seen_34_8_0 = cert50_layer_34_8_0 := by
  decide

def cert50_seen_34_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_34_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_34_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 34 [])
      LColor.r LColor.p cert50_seen_34_8_1 = cert50_layer_34_8_1 := by
  decide

def cert50_seen_34_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_34_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_34_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 34 [])
      LColor.r LColor.p cert50_seen_34_8_2 = cert50_layer_34_8_2 := by
  decide

def cert50_seen_34_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_34_8_3 : List ChainEdge :=
  []

theorem cert50_layer_34_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 34 [])
      LColor.r LColor.p cert50_seen_34_8_3 = cert50_layer_34_8_3 := by
  decide

theorem cert50_component_34_8_eq :
    closedCollarComponent word (listGetD fiber50 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_34_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 34 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 34 [])
      LColor.r LColor.p 27 cert50_seen_34_8_0 = cert50_component_34_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 34 []) LColor.r LColor.p
    cert50_seen_34_8_0 cert50_layer_34_8_0 26 cert50_layer_34_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 34 [])
      LColor.r LColor.p 26 cert50_seen_34_8_1 = cert50_component_34_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 34 []) LColor.r LColor.p
    cert50_seen_34_8_1 cert50_layer_34_8_1 25 cert50_layer_34_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 34 [])
      LColor.r LColor.p 25 cert50_seen_34_8_2 = cert50_component_34_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 34 []) LColor.r LColor.p
    cert50_seen_34_8_2 cert50_layer_34_8_2 24 cert50_layer_34_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 34 [])
      LColor.r LColor.p 24 cert50_seen_34_8_3 = cert50_component_34_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 34 []) LColor.r LColor.p
    cert50_seen_34_8_3 cert50_layer_34_8_3_eq 24

theorem cert50_step_34_8 :
    closedCollarIndexStepBool word fiber50 34 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_34_8)
    (by decide) (by decide)
    (by simpa [cert50_move_34_8] using cert50_component_34_8_eq)
    (by decide) (by decide) (by decide)

def cert50_move_35_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_35_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_35_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_35_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_35_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 35 [])
      LColor.r LColor.p cert50_seen_35_9_0 = cert50_layer_35_9_0 := by
  decide

def cert50_seen_35_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_35_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_35_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 35 [])
      LColor.r LColor.p cert50_seen_35_9_1 = cert50_layer_35_9_1 := by
  decide

def cert50_seen_35_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_35_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_35_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 35 [])
      LColor.r LColor.p cert50_seen_35_9_2 = cert50_layer_35_9_2 := by
  decide

def cert50_seen_35_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_35_9_3 : List ChainEdge :=
  []

theorem cert50_layer_35_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 35 [])
      LColor.r LColor.p cert50_seen_35_9_3 = cert50_layer_35_9_3 := by
  decide

theorem cert50_component_35_9_eq :
    closedCollarComponent word (listGetD fiber50 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_35_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 35 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 35 [])
      LColor.r LColor.p 27 cert50_seen_35_9_0 = cert50_component_35_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 35 []) LColor.r LColor.p
    cert50_seen_35_9_0 cert50_layer_35_9_0 26 cert50_layer_35_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 35 [])
      LColor.r LColor.p 26 cert50_seen_35_9_1 = cert50_component_35_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 35 []) LColor.r LColor.p
    cert50_seen_35_9_1 cert50_layer_35_9_1 25 cert50_layer_35_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 35 [])
      LColor.r LColor.p 25 cert50_seen_35_9_2 = cert50_component_35_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 35 []) LColor.r LColor.p
    cert50_seen_35_9_2 cert50_layer_35_9_2 24 cert50_layer_35_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 35 [])
      LColor.r LColor.p 24 cert50_seen_35_9_3 = cert50_component_35_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 35 []) LColor.r LColor.p
    cert50_seen_35_9_3 cert50_layer_35_9_3_eq 24

theorem cert50_step_35_9 :
    closedCollarIndexStepBool word fiber50 35 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_35_9)
    (by decide) (by decide)
    (by simpa [cert50_move_35_9] using cert50_component_35_9_eq)
    (by decide) (by decide) (by decide)

def cert50_move_36_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_36_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_36_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_36_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_36_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 36 [])
      LColor.r LColor.p cert50_seen_36_10_0 = cert50_layer_36_10_0 := by
  decide

def cert50_seen_36_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_36_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_36_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 36 [])
      LColor.r LColor.p cert50_seen_36_10_1 = cert50_layer_36_10_1 := by
  decide

def cert50_seen_36_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_36_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_36_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 36 [])
      LColor.r LColor.p cert50_seen_36_10_2 = cert50_layer_36_10_2 := by
  decide

def cert50_seen_36_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_36_10_3 : List ChainEdge :=
  []

theorem cert50_layer_36_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 36 [])
      LColor.r LColor.p cert50_seen_36_10_3 = cert50_layer_36_10_3 := by
  decide

theorem cert50_component_36_10_eq :
    closedCollarComponent word (listGetD fiber50 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_36_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 36 [])
      LColor.r LColor.p 27 cert50_seen_36_10_0 = cert50_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 36 []) LColor.r LColor.p
    cert50_seen_36_10_0 cert50_layer_36_10_0 26 cert50_layer_36_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 36 [])
      LColor.r LColor.p 26 cert50_seen_36_10_1 = cert50_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 36 []) LColor.r LColor.p
    cert50_seen_36_10_1 cert50_layer_36_10_1 25 cert50_layer_36_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 36 [])
      LColor.r LColor.p 25 cert50_seen_36_10_2 = cert50_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 36 []) LColor.r LColor.p
    cert50_seen_36_10_2 cert50_layer_36_10_2 24 cert50_layer_36_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 36 [])
      LColor.r LColor.p 24 cert50_seen_36_10_3 = cert50_component_36_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 36 []) LColor.r LColor.p
    cert50_seen_36_10_3 cert50_layer_36_10_3_eq 24

theorem cert50_step_36_10 :
    closedCollarIndexStepBool word fiber50 36 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_36_10)
    (by decide) (by decide)
    (by simpa [cert50_move_36_10] using cert50_component_36_10_eq)
    (by decide) (by decide) (by decide)

def cert50_move_37_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_37_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_seen_37_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_37_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_37_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 37 [])
      LColor.r LColor.p cert50_seen_37_11_0 = cert50_layer_37_11_0 := by
  decide

def cert50_seen_37_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_37_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_37_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 37 [])
      LColor.r LColor.p cert50_seen_37_11_1 = cert50_layer_37_11_1 := by
  decide

def cert50_seen_37_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_37_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert50_layer_37_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 37 [])
      LColor.r LColor.p cert50_seen_37_11_2 = cert50_layer_37_11_2 := by
  decide

def cert50_seen_37_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert50_layer_37_11_3 : List ChainEdge :=
  []

theorem cert50_layer_37_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 37 [])
      LColor.r LColor.p cert50_seen_37_11_3 = cert50_layer_37_11_3 := by
  decide

theorem cert50_component_37_11_eq :
    closedCollarComponent word (listGetD fiber50 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_37_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 37 [])
      LColor.r LColor.p 27 cert50_seen_37_11_0 = cert50_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 37 []) LColor.r LColor.p
    cert50_seen_37_11_0 cert50_layer_37_11_0 26 cert50_layer_37_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 37 [])
      LColor.r LColor.p 26 cert50_seen_37_11_1 = cert50_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 37 []) LColor.r LColor.p
    cert50_seen_37_11_1 cert50_layer_37_11_1 25 cert50_layer_37_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 37 [])
      LColor.r LColor.p 25 cert50_seen_37_11_2 = cert50_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 37 []) LColor.r LColor.p
    cert50_seen_37_11_2 cert50_layer_37_11_2 24 cert50_layer_37_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 37 [])
      LColor.r LColor.p 24 cert50_seen_37_11_3 = cert50_component_37_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 37 []) LColor.r LColor.p
    cert50_seen_37_11_3 cert50_layer_37_11_3_eq 24

theorem cert50_step_37_11 :
    closedCollarIndexStepBool word fiber50 37 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_37_11)
    (by decide) (by decide)
    (by simpa [cert50_move_37_11] using cert50_component_37_11_eq)
    (by decide) (by decide) (by decide)

def cert50_move_38_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_38_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_38_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_38_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 38 [])
      LColor.r LColor.p cert50_seen_38_0_0 = cert50_layer_38_0_0 := by
  decide

def cert50_seen_38_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_38_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_38_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 38 [])
      LColor.r LColor.p cert50_seen_38_0_1 = cert50_layer_38_0_1 := by
  decide

def cert50_seen_38_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_38_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_38_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 38 [])
      LColor.r LColor.p cert50_seen_38_0_2 = cert50_layer_38_0_2 := by
  decide

def cert50_seen_38_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_38_0_3 : List ChainEdge :=
  []

theorem cert50_layer_38_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 38 [])
      LColor.r LColor.p cert50_seen_38_0_3 = cert50_layer_38_0_3 := by
  decide

theorem cert50_component_38_0_eq :
    closedCollarComponent word (listGetD fiber50 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_38_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 38 [])
      LColor.r LColor.p 27 cert50_seen_38_0_0 = cert50_component_38_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 38 []) LColor.r LColor.p
    cert50_seen_38_0_0 cert50_layer_38_0_0 26 cert50_layer_38_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 38 [])
      LColor.r LColor.p 26 cert50_seen_38_0_1 = cert50_component_38_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 38 []) LColor.r LColor.p
    cert50_seen_38_0_1 cert50_layer_38_0_1 25 cert50_layer_38_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 38 [])
      LColor.r LColor.p 25 cert50_seen_38_0_2 = cert50_component_38_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 38 []) LColor.r LColor.p
    cert50_seen_38_0_2 cert50_layer_38_0_2 24 cert50_layer_38_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 38 [])
      LColor.r LColor.p 24 cert50_seen_38_0_3 = cert50_component_38_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 38 []) LColor.r LColor.p
    cert50_seen_38_0_3 cert50_layer_38_0_3_eq 24

theorem cert50_step_38_0 :
    closedCollarIndexStepBool word fiber50 38 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_38_0)
    (by decide) (by decide)
    (by simpa [cert50_move_38_0] using cert50_component_38_0_eq)
    (by decide) (by decide) (by decide)

def cert50_move_39_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_39_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_39_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_39_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 39 [])
      LColor.r LColor.p cert50_seen_39_1_0 = cert50_layer_39_1_0 := by
  decide

def cert50_seen_39_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_39_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_39_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 39 [])
      LColor.r LColor.p cert50_seen_39_1_1 = cert50_layer_39_1_1 := by
  decide

def cert50_seen_39_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_39_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_39_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 39 [])
      LColor.r LColor.p cert50_seen_39_1_2 = cert50_layer_39_1_2 := by
  decide

def cert50_seen_39_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_39_1_3 : List ChainEdge :=
  []

theorem cert50_layer_39_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 39 [])
      LColor.r LColor.p cert50_seen_39_1_3 = cert50_layer_39_1_3 := by
  decide

theorem cert50_component_39_1_eq :
    closedCollarComponent word (listGetD fiber50 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_39_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 39 [])
      LColor.r LColor.p 27 cert50_seen_39_1_0 = cert50_component_39_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 39 []) LColor.r LColor.p
    cert50_seen_39_1_0 cert50_layer_39_1_0 26 cert50_layer_39_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 39 [])
      LColor.r LColor.p 26 cert50_seen_39_1_1 = cert50_component_39_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 39 []) LColor.r LColor.p
    cert50_seen_39_1_1 cert50_layer_39_1_1 25 cert50_layer_39_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 39 [])
      LColor.r LColor.p 25 cert50_seen_39_1_2 = cert50_component_39_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 39 []) LColor.r LColor.p
    cert50_seen_39_1_2 cert50_layer_39_1_2 24 cert50_layer_39_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 39 [])
      LColor.r LColor.p 24 cert50_seen_39_1_3 = cert50_component_39_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 39 []) LColor.r LColor.p
    cert50_seen_39_1_3 cert50_layer_39_1_3_eq 24

theorem cert50_step_39_1 :
    closedCollarIndexStepBool word fiber50 39 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_39_1)
    (by decide) (by decide)
    (by simpa [cert50_move_39_1] using cert50_component_39_1_eq)
    (by decide) (by decide) (by decide)

def cert50_move_40_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_40_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_40_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_40_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.r LColor.p cert50_seen_40_2_0 = cert50_layer_40_2_0 := by
  decide

def cert50_seen_40_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_40_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_40_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.r LColor.p cert50_seen_40_2_1 = cert50_layer_40_2_1 := by
  decide

def cert50_seen_40_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_40_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_40_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.r LColor.p cert50_seen_40_2_2 = cert50_layer_40_2_2 := by
  decide

def cert50_seen_40_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_40_2_3 : List ChainEdge :=
  []

theorem cert50_layer_40_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.r LColor.p cert50_seen_40_2_3 = cert50_layer_40_2_3 := by
  decide

theorem cert50_component_40_2_eq :
    closedCollarComponent word (listGetD fiber50 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_40_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.r LColor.p 27 cert50_seen_40_2_0 = cert50_component_40_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.r LColor.p
    cert50_seen_40_2_0 cert50_layer_40_2_0 26 cert50_layer_40_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.r LColor.p 26 cert50_seen_40_2_1 = cert50_component_40_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.r LColor.p
    cert50_seen_40_2_1 cert50_layer_40_2_1 25 cert50_layer_40_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.r LColor.p 25 cert50_seen_40_2_2 = cert50_component_40_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.r LColor.p
    cert50_seen_40_2_2 cert50_layer_40_2_2 24 cert50_layer_40_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.r LColor.p 24 cert50_seen_40_2_3 = cert50_component_40_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 40 []) LColor.r LColor.p
    cert50_seen_40_2_3 cert50_layer_40_2_3_eq 24

theorem cert50_step_40_2 :
    closedCollarIndexStepBool word fiber50 40 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_40_2)
    (by decide) (by decide)
    (by simpa [cert50_move_40_2] using cert50_component_40_2_eq)
    (by decide) (by decide) (by decide)

def cert50_move_40_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_40_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_seen_40_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_40_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_40_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_0 = cert50_layer_40_28_0 := by
  decide

def cert50_seen_40_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_40_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_40_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_1 = cert50_layer_40_28_1 := by
  decide

def cert50_seen_40_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_40_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_40_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_2 = cert50_layer_40_28_2 := by
  decide

def cert50_seen_40_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_40_28_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert50_layer_40_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_3 = cert50_layer_40_28_3 := by
  decide

def cert50_seen_40_28_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert50_layer_40_28_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert50_layer_40_28_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_4 = cert50_layer_40_28_4 := by
  decide

def cert50_seen_40_28_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_40_28_5 : List ChainEdge :=
  []

theorem cert50_layer_40_28_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 40 [])
      LColor.b LColor.p cert50_seen_40_28_5 = cert50_layer_40_28_5 := by
  decide

theorem cert50_component_40_28_eq :
    closedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_40_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 27 cert50_seen_40_28_0 = cert50_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_0 cert50_layer_40_28_0 26 cert50_layer_40_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 26 cert50_seen_40_28_1 = cert50_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_1 cert50_layer_40_28_1 25 cert50_layer_40_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 25 cert50_seen_40_28_2 = cert50_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_2 cert50_layer_40_28_2 24 cert50_layer_40_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 24 cert50_seen_40_28_3 = cert50_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_3 cert50_layer_40_28_3 23 cert50_layer_40_28_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 23 cert50_seen_40_28_4 = cert50_component_40_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_4 cert50_layer_40_28_4 22 cert50_layer_40_28_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 40 [])
      LColor.b LColor.p 22 cert50_seen_40_28_5 = cert50_component_40_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 40 []) LColor.b LColor.p
    cert50_seen_40_28_5 cert50_layer_40_28_5_eq 22

theorem cert50_step_40_28 :
    closedCollarIndexStepBool word fiber50 40 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_40_28)
    (by decide) (by decide)
    (by simpa [cert50_move_40_28] using cert50_component_40_28_eq)
    (by decide) (by decide) (by decide)

def cert50_move_41_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_41_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_41_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_41_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.r LColor.p cert50_seen_41_3_0 = cert50_layer_41_3_0 := by
  decide

def cert50_seen_41_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_41_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_41_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.r LColor.p cert50_seen_41_3_1 = cert50_layer_41_3_1 := by
  decide

def cert50_seen_41_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_41_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_41_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.r LColor.p cert50_seen_41_3_2 = cert50_layer_41_3_2 := by
  decide

def cert50_seen_41_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_41_3_3 : List ChainEdge :=
  []

theorem cert50_layer_41_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.r LColor.p cert50_seen_41_3_3 = cert50_layer_41_3_3 := by
  decide

theorem cert50_component_41_3_eq :
    closedCollarComponent word (listGetD fiber50 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_41_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.r LColor.p 27 cert50_seen_41_3_0 = cert50_component_41_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.r LColor.p
    cert50_seen_41_3_0 cert50_layer_41_3_0 26 cert50_layer_41_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.r LColor.p 26 cert50_seen_41_3_1 = cert50_component_41_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.r LColor.p
    cert50_seen_41_3_1 cert50_layer_41_3_1 25 cert50_layer_41_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.r LColor.p 25 cert50_seen_41_3_2 = cert50_component_41_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.r LColor.p
    cert50_seen_41_3_2 cert50_layer_41_3_2 24 cert50_layer_41_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.r LColor.p 24 cert50_seen_41_3_3 = cert50_component_41_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 41 []) LColor.r LColor.p
    cert50_seen_41_3_3 cert50_layer_41_3_3_eq 24

theorem cert50_step_41_3 :
    closedCollarIndexStepBool word fiber50 41 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_41_3)
    (by decide) (by decide)
    (by simpa [cert50_move_41_3] using cert50_component_41_3_eq)
    (by decide) (by decide) (by decide)

def cert50_move_41_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_41_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_seen_41_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_41_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_41_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_0 = cert50_layer_41_29_0 := by
  decide

def cert50_seen_41_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_41_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert50_layer_41_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_1 = cert50_layer_41_29_1 := by
  decide

def cert50_seen_41_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert50_layer_41_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert50_layer_41_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_2 = cert50_layer_41_29_2 := by
  decide

def cert50_seen_41_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert50_layer_41_29_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert50_layer_41_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_3 = cert50_layer_41_29_3 := by
  decide

def cert50_seen_41_29_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert50_layer_41_29_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert50_layer_41_29_4_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_4 = cert50_layer_41_29_4 := by
  decide

def cert50_seen_41_29_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert50_layer_41_29_5 : List ChainEdge :=
  []

theorem cert50_layer_41_29_5_eq :
    closedCollarComponentLayer word (listGetD fiber50 41 [])
      LColor.b LColor.p cert50_seen_41_29_5 = cert50_layer_41_29_5 := by
  decide

theorem cert50_component_41_29_eq :
    closedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_41_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 27 cert50_seen_41_29_0 = cert50_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_0 cert50_layer_41_29_0 26 cert50_layer_41_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 26 cert50_seen_41_29_1 = cert50_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_1 cert50_layer_41_29_1 25 cert50_layer_41_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 25 cert50_seen_41_29_2 = cert50_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_2 cert50_layer_41_29_2 24 cert50_layer_41_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 24 cert50_seen_41_29_3 = cert50_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_3 cert50_layer_41_29_3 23 cert50_layer_41_29_3_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 23 cert50_seen_41_29_4 = cert50_component_41_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_4 cert50_layer_41_29_4 22 cert50_layer_41_29_4_eq]
  change closeClosedCollarComponent word (listGetD fiber50 41 [])
      LColor.b LColor.p 22 cert50_seen_41_29_5 = cert50_component_41_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 41 []) LColor.b LColor.p
    cert50_seen_41_29_5 cert50_layer_41_29_5_eq 22

theorem cert50_step_41_29 :
    closedCollarIndexStepBool word fiber50 41 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_41_29)
    (by decide) (by decide)
    (by simpa [cert50_move_41_29] using cert50_component_41_29_eq)
    (by decide) (by decide) (by decide)

def cert50_move_42_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_42_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_42_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_42_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_42_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.r LColor.p cert50_seen_42_4_0 = cert50_layer_42_4_0 := by
  decide

def cert50_seen_42_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_42_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_42_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.r LColor.p cert50_seen_42_4_1 = cert50_layer_42_4_1 := by
  decide

def cert50_seen_42_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_42_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_42_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.r LColor.p cert50_seen_42_4_2 = cert50_layer_42_4_2 := by
  decide

def cert50_seen_42_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_42_4_3 : List ChainEdge :=
  []

theorem cert50_layer_42_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.r LColor.p cert50_seen_42_4_3 = cert50_layer_42_4_3 := by
  decide

theorem cert50_component_42_4_eq :
    closedCollarComponent word (listGetD fiber50 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_42_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.r LColor.p 27 cert50_seen_42_4_0 = cert50_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.r LColor.p
    cert50_seen_42_4_0 cert50_layer_42_4_0 26 cert50_layer_42_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.r LColor.p 26 cert50_seen_42_4_1 = cert50_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.r LColor.p
    cert50_seen_42_4_1 cert50_layer_42_4_1 25 cert50_layer_42_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.r LColor.p 25 cert50_seen_42_4_2 = cert50_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.r LColor.p
    cert50_seen_42_4_2 cert50_layer_42_4_2 24 cert50_layer_42_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.r LColor.p 24 cert50_seen_42_4_3 = cert50_component_42_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 42 []) LColor.r LColor.p
    cert50_seen_42_4_3 cert50_layer_42_4_3_eq 24

theorem cert50_step_42_4 :
    closedCollarIndexStepBool word fiber50 42 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_42_4)
    (by decide) (by decide)
    (by simpa [cert50_move_42_4] using cert50_component_42_4_eq)
    (by decide) (by decide) (by decide)

def cert50_move_42_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_42_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_42_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_42_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_42_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.b LColor.p cert50_seen_42_30_0 = cert50_layer_42_30_0 := by
  decide

def cert50_seen_42_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_42_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_42_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.b LColor.p cert50_seen_42_30_1 = cert50_layer_42_30_1 := by
  decide

def cert50_seen_42_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_42_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_42_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.b LColor.p cert50_seen_42_30_2 = cert50_layer_42_30_2 := by
  decide

def cert50_seen_42_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_42_30_3 : List ChainEdge :=
  []

theorem cert50_layer_42_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 42 [])
      LColor.b LColor.p cert50_seen_42_30_3 = cert50_layer_42_30_3 := by
  decide

theorem cert50_component_42_30_eq :
    closedCollarComponent word (listGetD fiber50 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_42_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.b LColor.p 27 cert50_seen_42_30_0 = cert50_component_42_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.b LColor.p
    cert50_seen_42_30_0 cert50_layer_42_30_0 26 cert50_layer_42_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.b LColor.p 26 cert50_seen_42_30_1 = cert50_component_42_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.b LColor.p
    cert50_seen_42_30_1 cert50_layer_42_30_1 25 cert50_layer_42_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.b LColor.p 25 cert50_seen_42_30_2 = cert50_component_42_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 42 []) LColor.b LColor.p
    cert50_seen_42_30_2 cert50_layer_42_30_2 24 cert50_layer_42_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 42 [])
      LColor.b LColor.p 24 cert50_seen_42_30_3 = cert50_component_42_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 42 []) LColor.b LColor.p
    cert50_seen_42_30_3 cert50_layer_42_30_3_eq 24

theorem cert50_step_42_30 :
    closedCollarIndexStepBool word fiber50 42 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_42_30)
    (by decide) (by decide)
    (by simpa [cert50_move_42_30] using cert50_component_42_30_eq)
    (by decide) (by decide) (by decide)

def cert50_move_43_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert50_component_43_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_seen_43_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert50_layer_43_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert50_layer_43_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.r LColor.p cert50_seen_43_5_0 = cert50_layer_43_5_0 := by
  decide

def cert50_seen_43_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert50_layer_43_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert50_layer_43_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.r LColor.p cert50_seen_43_5_1 = cert50_layer_43_5_1 := by
  decide

def cert50_seen_43_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert50_layer_43_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert50_layer_43_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.r LColor.p cert50_seen_43_5_2 = cert50_layer_43_5_2 := by
  decide

def cert50_seen_43_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert50_layer_43_5_3 : List ChainEdge :=
  []

theorem cert50_layer_43_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.r LColor.p cert50_seen_43_5_3 = cert50_layer_43_5_3 := by
  decide

theorem cert50_component_43_5_eq :
    closedCollarComponent word (listGetD fiber50 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert50_component_43_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.r LColor.p 27 cert50_seen_43_5_0 = cert50_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.r LColor.p
    cert50_seen_43_5_0 cert50_layer_43_5_0 26 cert50_layer_43_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.r LColor.p 26 cert50_seen_43_5_1 = cert50_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.r LColor.p
    cert50_seen_43_5_1 cert50_layer_43_5_1 25 cert50_layer_43_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.r LColor.p 25 cert50_seen_43_5_2 = cert50_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.r LColor.p
    cert50_seen_43_5_2 cert50_layer_43_5_2 24 cert50_layer_43_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.r LColor.p 24 cert50_seen_43_5_3 = cert50_component_43_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 43 []) LColor.r LColor.p
    cert50_seen_43_5_3 cert50_layer_43_5_3_eq 24

theorem cert50_step_43_5 :
    closedCollarIndexStepBool word fiber50 43 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_43_5)
    (by decide) (by decide)
    (by simpa [cert50_move_43_5] using cert50_component_43_5_eq)
    (by decide) (by decide) (by decide)

def cert50_move_43_31 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert50_component_43_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_seen_43_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert50_layer_43_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert50_layer_43_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.b LColor.p cert50_seen_43_31_0 = cert50_layer_43_31_0 := by
  decide

def cert50_seen_43_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert50_layer_43_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert50_layer_43_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.b LColor.p cert50_seen_43_31_1 = cert50_layer_43_31_1 := by
  decide

def cert50_seen_43_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert50_layer_43_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert50_layer_43_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.b LColor.p cert50_seen_43_31_2 = cert50_layer_43_31_2 := by
  decide

def cert50_seen_43_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert50_layer_43_31_3 : List ChainEdge :=
  []

theorem cert50_layer_43_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber50 43 [])
      LColor.b LColor.p cert50_seen_43_31_3 = cert50_layer_43_31_3 := by
  decide

theorem cert50_component_43_31_eq :
    closedCollarComponent word (listGetD fiber50 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert50_component_43_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber50 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.b LColor.p 27 cert50_seen_43_31_0 = cert50_component_43_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.b LColor.p
    cert50_seen_43_31_0 cert50_layer_43_31_0 26 cert50_layer_43_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.b LColor.p 26 cert50_seen_43_31_1 = cert50_component_43_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.b LColor.p
    cert50_seen_43_31_1 cert50_layer_43_31_1 25 cert50_layer_43_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.b LColor.p 25 cert50_seen_43_31_2 = cert50_component_43_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber50 43 []) LColor.b LColor.p
    cert50_seen_43_31_2 cert50_layer_43_31_2 24 cert50_layer_43_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber50 43 [])
      LColor.b LColor.p 24 cert50_seen_43_31_3 = cert50_component_43_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber50 43 []) LColor.b LColor.p
    cert50_seen_43_31_3 cert50_layer_43_31_3_eq 24

theorem cert50_step_43_31 :
    closedCollarIndexStepBool word fiber50 43 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert50_move_43_31)
    (by decide) (by decide)
    (by simpa [cert50_move_43_31] using cert50_component_43_31_eq)
    (by decide) (by decide) (by decide)

theorem cert50_row_0 :
    closedCollarParentIndexValid word fiber50 cert50.parents 0 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length]

theorem cert50_row_1 :
    closedCollarParentIndexValid word fiber50 cert50.parents 1 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_1_0, cert50_step_0_1]

theorem cert50_row_2 :
    closedCollarParentIndexValid word fiber50 cert50.parents 2 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_2_0, cert50_step_0_2]

theorem cert50_row_3 :
    closedCollarParentIndexValid word fiber50 cert50.parents 3 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_3_1, cert50_step_1_3]

theorem cert50_row_4 :
    closedCollarParentIndexValid word fiber50 cert50.parents 4 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_4_1, cert50_step_1_4]

theorem cert50_row_5 :
    closedCollarParentIndexValid word fiber50 cert50.parents 5 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_5_0, cert50_step_0_5]

theorem cert50_row_6 :
    closedCollarParentIndexValid word fiber50 cert50.parents 6 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_6_0, cert50_step_0_6]

theorem cert50_row_7 :
    closedCollarParentIndexValid word fiber50 cert50.parents 7 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_7_1, cert50_step_1_7]

theorem cert50_row_8 :
    closedCollarParentIndexValid word fiber50 cert50.parents 8 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_8_2, cert50_step_2_8]

theorem cert50_row_9 :
    closedCollarParentIndexValid word fiber50 cert50.parents 9 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_9_3, cert50_step_3_9]

theorem cert50_row_10 :
    closedCollarParentIndexValid word fiber50 cert50.parents 10 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_10_4, cert50_step_4_10]

theorem cert50_row_11 :
    closedCollarParentIndexValid word fiber50 cert50.parents 11 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_11_5, cert50_step_5_11]

theorem cert50_row_12 :
    closedCollarParentIndexValid word fiber50 cert50.parents 12 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_12_0, cert50_step_0_12]

theorem cert50_row_13 :
    closedCollarParentIndexValid word fiber50 cert50.parents 13 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_13_1, cert50_step_1_13]

theorem cert50_row_14 :
    closedCollarParentIndexValid word fiber50 cert50.parents 14 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_14_2, cert50_step_2_14]

theorem cert50_row_15 :
    closedCollarParentIndexValid word fiber50 cert50.parents 15 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_15_3, cert50_step_3_15]

theorem cert50_row_16 :
    closedCollarParentIndexValid word fiber50 cert50.parents 16 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_16_4, cert50_step_4_16]

theorem cert50_row_17 :
    closedCollarParentIndexValid word fiber50 cert50.parents 17 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_17_5, cert50_step_5_17]

theorem cert50_row_18 :
    closedCollarParentIndexValid word fiber50 cert50.parents 18 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_18_6, cert50_step_6_18]

theorem cert50_row_19 :
    closedCollarParentIndexValid word fiber50 cert50.parents 19 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_19_7, cert50_step_7_19]

theorem cert50_row_20 :
    closedCollarParentIndexValid word fiber50 cert50.parents 20 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_20_8, cert50_step_8_20]

theorem cert50_row_21 :
    closedCollarParentIndexValid word fiber50 cert50.parents 21 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_21_9, cert50_step_9_21]

theorem cert50_row_22 :
    closedCollarParentIndexValid word fiber50 cert50.parents 22 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_22_10, cert50_step_10_22]

theorem cert50_row_23 :
    closedCollarParentIndexValid word fiber50 cert50.parents 23 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_23_11, cert50_step_11_23]

theorem cert50_row_24 :
    closedCollarParentIndexValid word fiber50 cert50.parents 24 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_24_16, cert50_step_16_24]

theorem cert50_row_25 :
    closedCollarParentIndexValid word fiber50 cert50.parents 25 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_25_17, cert50_step_17_25]

theorem cert50_row_26 :
    closedCollarParentIndexValid word fiber50 cert50.parents 26 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_26_13, cert50_step_13_26]

theorem cert50_row_27 :
    closedCollarParentIndexValid word fiber50 cert50.parents 27 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_27_12, cert50_step_12_27]

theorem cert50_row_28 :
    closedCollarParentIndexValid word fiber50 cert50.parents 28 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_28_40, cert50_step_40_28]

theorem cert50_row_29 :
    closedCollarParentIndexValid word fiber50 cert50.parents 29 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_29_41, cert50_step_41_29]

theorem cert50_row_30 :
    closedCollarParentIndexValid word fiber50 cert50.parents 30 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_30_42, cert50_step_42_30]

theorem cert50_row_31 :
    closedCollarParentIndexValid word fiber50 cert50.parents 31 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_31_43, cert50_step_43_31]

theorem cert50_row_32 :
    closedCollarParentIndexValid word fiber50 cert50.parents 32 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_32_6, cert50_step_6_32]

theorem cert50_row_33 :
    closedCollarParentIndexValid word fiber50 cert50.parents 33 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_33_7, cert50_step_7_33]

theorem cert50_row_34 :
    closedCollarParentIndexValid word fiber50 cert50.parents 34 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_34_8, cert50_step_8_34]

theorem cert50_row_35 :
    closedCollarParentIndexValid word fiber50 cert50.parents 35 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_35_9, cert50_step_9_35]

theorem cert50_row_36 :
    closedCollarParentIndexValid word fiber50 cert50.parents 36 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_36_10, cert50_step_10_36]

theorem cert50_row_37 :
    closedCollarParentIndexValid word fiber50 cert50.parents 37 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_37_11, cert50_step_11_37]

theorem cert50_row_38 :
    closedCollarParentIndexValid word fiber50 cert50.parents 38 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_38_0, cert50_step_0_38]

theorem cert50_row_39 :
    closedCollarParentIndexValid word fiber50 cert50.parents 39 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_39_1, cert50_step_1_39]

theorem cert50_row_40 :
    closedCollarParentIndexValid word fiber50 cert50.parents 40 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_40_2, cert50_step_2_40]

theorem cert50_row_41 :
    closedCollarParentIndexValid word fiber50 cert50.parents 41 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_41_3, cert50_step_3_41]

theorem cert50_row_42 :
    closedCollarParentIndexValid word fiber50 cert50.parents 42 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_42_4, cert50_step_4_42]

theorem cert50_row_43 :
    closedCollarParentIndexValid word fiber50 cert50.parents 43 = true := by
  have cert50_fiber_length : fiber50.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert50, listGetD, cert50_fiber_length, cert50_step_43_5, cert50_step_5_43]

theorem cert50_rows :
    closedCollarSpineRowsValid word fiber50 cert50.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert50_fiber_length : fiber50.length = 44 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert50_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert50_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert50_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert50_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert50_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert50_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert50_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert50_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert50_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert50_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert50_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert50_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert50_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert50_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert50_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert50_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert50_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert50_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert50_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert50_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert50_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert50_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert50_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert50_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert50_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert50_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert50_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert50_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert50_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert50_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert50_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert50_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert50_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert50_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert50_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert50_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert50_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert50_row_43
  · omega

theorem cert50_root :
    closedCollarSpineParentsReachRoot fiber50 cert50 = true := by
  decide

theorem cert50_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.p] := by
  change closedCollarFiberKempeConnected word cert50.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert50 fiber50_eq cert50_rows cert50_root


end GoertzelLemma818ClosedCollarS2Word11
end Mettapedia.GraphTheory.FourColor
