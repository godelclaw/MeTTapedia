import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word11

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast20 : List TauState :=
  [stateAt 2, stateAt 10, stateAt 18, stateAt 26, stateAt 66, stateAt 74, stateAt 82, stateAt 90]

theorem keyedLast20_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.r, LColor.p]) =
      keyedLast20 := by
  decide

def fiber20OuterChunks : List (List (List TauState)) :=
[
  []
, [
  [stateAt 16, stateAt 80, stateAt 82]
, [stateAt 16, stateAt 81, stateAt 90]
, [stateAt 16, stateAt 82, stateAt 18]
, [stateAt 16, stateAt 83, stateAt 26]
, [stateAt 16, stateAt 102, stateAt 66]
, [stateAt 16, stateAt 103, stateAt 74]
, [stateAt 17, stateAt 88, stateAt 82]
, [stateAt 17, stateAt 89, stateAt 90]
, [stateAt 17, stateAt 90, stateAt 18]
, [stateAt 17, stateAt 91, stateAt 26]
, [stateAt 17, stateAt 110, stateAt 66]
, [stateAt 17, stateAt 111, stateAt 74]
, [stateAt 18, stateAt 16, stateAt 82]
, [stateAt 18, stateAt 17, stateAt 90]
, [stateAt 18, stateAt 18, stateAt 18]
, [stateAt 18, stateAt 19, stateAt 26]
, [stateAt 18, stateAt 34, stateAt 2]
, [stateAt 18, stateAt 35, stateAt 10]
, [stateAt 19, stateAt 24, stateAt 82]
, [stateAt 19, stateAt 25, stateAt 90]
, [stateAt 19, stateAt 26, stateAt 18]
, [stateAt 19, stateAt 27, stateAt 26]
, [stateAt 19, stateAt 42, stateAt 2]
, [stateAt 19, stateAt 43, stateAt 10]
]
, [
  [stateAt 32, stateAt 150, stateAt 2]
, [stateAt 32, stateAt 151, stateAt 10]
, [stateAt 32, stateAt 166, stateAt 66]
, [stateAt 32, stateAt 167, stateAt 74]
, [stateAt 33, stateAt 158, stateAt 2]
, [stateAt 33, stateAt 159, stateAt 10]
, [stateAt 33, stateAt 174, stateAt 66]
, [stateAt 33, stateAt 175, stateAt 74]
, [stateAt 34, stateAt 0, stateAt 82]
, [stateAt 34, stateAt 1, stateAt 90]
, [stateAt 34, stateAt 2, stateAt 18]
, [stateAt 34, stateAt 3, stateAt 26]
, [stateAt 34, stateAt 50, stateAt 2]
, [stateAt 34, stateAt 51, stateAt 10]
, [stateAt 35, stateAt 8, stateAt 82]
, [stateAt 35, stateAt 9, stateAt 90]
, [stateAt 35, stateAt 10, stateAt 18]
, [stateAt 35, stateAt 11, stateAt 26]
, [stateAt 35, stateAt 58, stateAt 2]
, [stateAt 35, stateAt 59, stateAt 10]
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

def fiber20 : List (List TauState) :=
  fiber20OuterChunks.flatten

theorem fiber20_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 0 []) =
      listGetD fiber20OuterChunks 0 [] := by
  decide

theorem fiber20_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 1 []) =
      listGetD fiber20OuterChunks 1 [] := by
  decide

theorem fiber20_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 2 []) =
      listGetD fiber20OuterChunks 2 [] := by
  decide

theorem fiber20_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 3 []) =
      listGetD fiber20OuterChunks 3 [] := by
  decide

theorem fiber20_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 4 []) =
      listGetD fiber20OuterChunks 4 [] := by
  decide

theorem fiber20_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 5 []) =
      listGetD fiber20OuterChunks 5 [] := by
  decide

theorem fiber20_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 6 []) =
      listGetD fiber20OuterChunks 6 [] := by
  decide

theorem fiber20_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 7 []) =
      listGetD fiber20OuterChunks 7 [] := by
  decide

theorem fiber20_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 8 []) =
      listGetD fiber20OuterChunks 8 [] := by
  decide

theorem fiber20_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 9 []) =
      listGetD fiber20OuterChunks 9 [] := by
  decide

theorem fiber20_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 10 []) =
      listGetD fiber20OuterChunks 10 [] := by
  decide

theorem fiber20_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks 11 []) =
      listGetD fiber20OuterChunks 11 [] := by
  decide

theorem fiber20_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast20
        (listGetD tauStateChunks idx []) =
      listGetD fiber20OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber20_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber20_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber20_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber20_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber20_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber20_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber20_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber20_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber20_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber20_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber20_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber20_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber20_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast20 =
      fiber20 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast20 tauStateChunks fiber20OuterChunks
    tauStateChunks_eq (by rfl) fiber20_outer_get
  simpa [fiber20] using h

theorem fiber20_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.r, LColor.p] = fiber20 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.r, LColor.p] keyedLast20_eq
  exact hfrom.trans fiber20_keyedFrom_eq

theorem fiber20_eq :
    closedCollarFiber word [LColor.r, LColor.p, LColor.r, LColor.p] = fiber20 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.mirror [LColor.r, LColor.p, LColor.r, LColor.p]
  exact hfast.trans fiber20_keyed_eq

def cert20 : ClosedCollarSpineCertificate :=
  { key := [LColor.r, LColor.p, LColor.r, LColor.p],
    root := 0,
    maxDepth := 5,
    parents := [0, 0, 0, 1, 1, 0, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 27, 26, 20, 21, 24, 25] }

def cert20_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert20_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert20_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_1_0 = cert20_layer_0_1_0 := by
  decide

def cert20_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_0_1_1 : List ChainEdge :=
  []

theorem cert20_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_1_1 = cert20_layer_0_1_1 := by
  decide

theorem cert20_component_0_1_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert20_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 27 cert20_seen_0_1_0 = cert20_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_1_0 cert20_layer_0_1_0 26 cert20_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 26 cert20_seen_0_1_1 = cert20_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_1_1 cert20_layer_0_1_1_eq 26

theorem cert20_step_0_1 :
    closedCollarIndexStepBool word fiber20 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_1)
    (by decide) (by decide)
    (by simpa [cert20_move_0_1] using cert20_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_0_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert20_component_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_seen_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_0_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_0_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_0 = cert20_layer_0_2_0 := by
  decide

def cert20_seen_0_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_0_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_0_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_1 = cert20_layer_0_2_1 := by
  decide

def cert20_seen_0_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_0_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_0_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_2 = cert20_layer_0_2_2 := by
  decide

def cert20_seen_0_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_0_2_3 : List ChainEdge :=
  []

theorem cert20_layer_0_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_2_3 = cert20_layer_0_2_3 := by
  decide

theorem cert20_component_0_2_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert20_component_0_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 27 cert20_seen_0_2_0 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_0 cert20_layer_0_2_0 26 cert20_layer_0_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 26 cert20_seen_0_2_1 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_1 cert20_layer_0_2_1 25 cert20_layer_0_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 25 cert20_seen_0_2_2 = cert20_component_0_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_2 cert20_layer_0_2_2 24 cert20_layer_0_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 24 cert20_seen_0_2_3 = cert20_component_0_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_2_3 cert20_layer_0_2_3_eq 24

theorem cert20_step_0_2 :
    closedCollarIndexStepBool word fiber20 0 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_2)
    (by decide) (by decide)
    (by simpa [cert20_move_0_2] using cert20_component_0_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_0_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert20_component_0_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_0_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_0_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.p cert20_seen_0_5_0 = cert20_layer_0_5_0 := by
  decide

def cert20_seen_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_0_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_0_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.p cert20_seen_0_5_1 = cert20_layer_0_5_1 := by
  decide

def cert20_seen_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_0_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_0_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.p cert20_seen_0_5_2 = cert20_layer_0_5_2 := by
  decide

def cert20_seen_0_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_0_5_3 : List ChainEdge :=
  []

theorem cert20_layer_0_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.p cert20_seen_0_5_3 = cert20_layer_0_5_3 := by
  decide

theorem cert20_component_0_5_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert20_component_0_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.p 27 cert20_seen_0_5_0 = cert20_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.p
    cert20_seen_0_5_0 cert20_layer_0_5_0 26 cert20_layer_0_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.p 26 cert20_seen_0_5_1 = cert20_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.p
    cert20_seen_0_5_1 cert20_layer_0_5_1 25 cert20_layer_0_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.p 25 cert20_seen_0_5_2 = cert20_component_0_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.p
    cert20_seen_0_5_2 cert20_layer_0_5_2 24 cert20_layer_0_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.p 24 cert20_seen_0_5_3 = cert20_component_0_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.r LColor.p
    cert20_seen_0_5_3 cert20_layer_0_5_3_eq 24

theorem cert20_step_0_5 :
    closedCollarIndexStepBool word fiber20 0 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_5)
    (by decide) (by decide)
    (by simpa [cert20_move_0_5] using cert20_component_0_5_eq)
    (by decide) (by decide) (by decide)

def cert20_move_0_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_6_0 = cert20_layer_0_6_0 := by
  decide

def cert20_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_0_6_1 : List ChainEdge :=
  []

theorem cert20_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.b LColor.p cert20_seen_0_6_1 = cert20_layer_0_6_1 := by
  decide

theorem cert20_component_0_6_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 27 cert20_seen_0_6_0 = cert20_component_0_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_6_0 cert20_layer_0_6_0 26 cert20_layer_0_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.b LColor.p 26 cert20_seen_0_6_1 = cert20_component_0_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.b LColor.p
    cert20_seen_0_6_1 cert20_layer_0_6_1_eq 26

theorem cert20_step_0_6 :
    closedCollarIndexStepBool word fiber20 0 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_6)
    (by decide) (by decide)
    (by simpa [cert20_move_0_6] using cert20_component_0_6_eq)
    (by decide) (by decide) (by decide)

def cert20_move_0_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_0_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_0_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_12_0 = cert20_layer_0_12_0 := by
  decide

def cert20_seen_0_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_0_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_0_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_12_1 = cert20_layer_0_12_1 := by
  decide

def cert20_seen_0_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_0_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_0_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_12_2 = cert20_layer_0_12_2 := by
  decide

def cert20_seen_0_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_0_12_3 : List ChainEdge :=
  []

theorem cert20_layer_0_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 0 [])
      LColor.r LColor.b cert20_seen_0_12_3 = cert20_layer_0_12_3 := by
  decide

theorem cert20_component_0_12_eq :
    closedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_0_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 27 cert20_seen_0_12_0 = cert20_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_12_0 cert20_layer_0_12_0 26 cert20_layer_0_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 26 cert20_seen_0_12_1 = cert20_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_12_1 cert20_layer_0_12_1 25 cert20_layer_0_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 25 cert20_seen_0_12_2 = cert20_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_12_2 cert20_layer_0_12_2 24 cert20_layer_0_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 0 [])
      LColor.r LColor.b 24 cert20_seen_0_12_3 = cert20_component_0_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 0 []) LColor.r LColor.b
    cert20_seen_0_12_3 cert20_layer_0_12_3_eq 24

theorem cert20_step_0_12 :
    closedCollarIndexStepBool word fiber20 0 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_0_12)
    (by decide) (by decide)
    (by simpa [cert20_move_0_12] using cert20_component_0_12_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B6 } }

def cert20_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

def cert20_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_0_0 = cert20_layer_1_0_0 := by
  decide

def cert20_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_1_0_1 : List ChainEdge :=
  []

theorem cert20_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_0_1 = cert20_layer_1_0_1 := by
  decide

theorem cert20_component_1_0_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = cert20_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 27 cert20_seen_1_0_0 = cert20_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_0_0 cert20_layer_1_0_0 26 cert20_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 26 cert20_seen_1_0_1 = cert20_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_0_1 cert20_layer_1_0_1_eq 26

theorem cert20_step_1_0 :
    closedCollarIndexStepBool word fiber20 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_0)
    (by decide) (by decide)
    (by simpa [cert20_move_1_0] using cert20_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert20_component_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_seen_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_1_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_1_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_0 = cert20_layer_1_3_0 := by
  decide

def cert20_seen_1_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_1_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_1_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_1 = cert20_layer_1_3_1 := by
  decide

def cert20_seen_1_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_1_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_1_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_2 = cert20_layer_1_3_2 := by
  decide

def cert20_seen_1_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_1_3_3 : List ChainEdge :=
  []

theorem cert20_layer_1_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_3_3 = cert20_layer_1_3_3 := by
  decide

theorem cert20_component_1_3_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert20_component_1_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 27 cert20_seen_1_3_0 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_0 cert20_layer_1_3_0 26 cert20_layer_1_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 26 cert20_seen_1_3_1 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_1 cert20_layer_1_3_1 25 cert20_layer_1_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 25 cert20_seen_1_3_2 = cert20_component_1_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_2 cert20_layer_1_3_2 24 cert20_layer_1_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 24 cert20_seen_1_3_3 = cert20_component_1_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_3_3 cert20_layer_1_3_3_eq 24

theorem cert20_step_1_3 :
    closedCollarIndexStepBool word fiber20 1 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_3)
    (by decide) (by decide)
    (by simpa [cert20_move_1_3] using cert20_component_1_3_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert20_component_1_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_1_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_1_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.p cert20_seen_1_4_0 = cert20_layer_1_4_0 := by
  decide

def cert20_seen_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_1_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_1_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.p cert20_seen_1_4_1 = cert20_layer_1_4_1 := by
  decide

def cert20_seen_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_1_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_1_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.p cert20_seen_1_4_2 = cert20_layer_1_4_2 := by
  decide

def cert20_seen_1_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_1_4_3 : List ChainEdge :=
  []

theorem cert20_layer_1_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.p cert20_seen_1_4_3 = cert20_layer_1_4_3 := by
  decide

theorem cert20_component_1_4_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert20_component_1_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.p 27 cert20_seen_1_4_0 = cert20_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.p
    cert20_seen_1_4_0 cert20_layer_1_4_0 26 cert20_layer_1_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.p 26 cert20_seen_1_4_1 = cert20_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.p
    cert20_seen_1_4_1 cert20_layer_1_4_1 25 cert20_layer_1_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.p 25 cert20_seen_1_4_2 = cert20_component_1_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.p
    cert20_seen_1_4_2 cert20_layer_1_4_2 24 cert20_layer_1_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.p 24 cert20_seen_1_4_3 = cert20_component_1_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.r LColor.p
    cert20_seen_1_4_3 cert20_layer_1_4_3_eq 24

theorem cert20_step_1_4 :
    closedCollarIndexStepBool word fiber20 1 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_4)
    (by decide) (by decide)
    (by simpa [cert20_move_1_4] using cert20_component_1_4_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_7_0 = cert20_layer_1_7_0 := by
  decide

def cert20_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_1_7_1 : List ChainEdge :=
  []

theorem cert20_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.b LColor.p cert20_seen_1_7_1 = cert20_layer_1_7_1 := by
  decide

theorem cert20_component_1_7_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 27 cert20_seen_1_7_0 = cert20_component_1_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_7_0 cert20_layer_1_7_0 26 cert20_layer_1_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.b LColor.p 26 cert20_seen_1_7_1 = cert20_component_1_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.b LColor.p
    cert20_seen_1_7_1 cert20_layer_1_7_1_eq 26

theorem cert20_step_1_7 :
    closedCollarIndexStepBool word fiber20 1 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_7)
    (by decide) (by decide)
    (by simpa [cert20_move_1_7] using cert20_component_1_7_eq)
    (by decide) (by decide) (by decide)

def cert20_move_1_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_1_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_1_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_13_0 = cert20_layer_1_13_0 := by
  decide

def cert20_seen_1_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_1_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_1_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_13_1 = cert20_layer_1_13_1 := by
  decide

def cert20_seen_1_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_1_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_1_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_13_2 = cert20_layer_1_13_2 := by
  decide

def cert20_seen_1_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_1_13_3 : List ChainEdge :=
  []

theorem cert20_layer_1_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 1 [])
      LColor.r LColor.b cert20_seen_1_13_3 = cert20_layer_1_13_3 := by
  decide

theorem cert20_component_1_13_eq :
    closedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_1_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 27 cert20_seen_1_13_0 = cert20_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_13_0 cert20_layer_1_13_0 26 cert20_layer_1_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 26 cert20_seen_1_13_1 = cert20_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_13_1 cert20_layer_1_13_1 25 cert20_layer_1_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 25 cert20_seen_1_13_2 = cert20_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_13_2 cert20_layer_1_13_2 24 cert20_layer_1_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 1 [])
      LColor.r LColor.b 24 cert20_seen_1_13_3 = cert20_component_1_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 1 []) LColor.r LColor.b
    cert20_seen_1_13_3 cert20_layer_1_13_3_eq 24

theorem cert20_step_1_13 :
    closedCollarIndexStepBool word fiber20 1 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_1_13)
    (by decide) (by decide)
    (by simpa [cert20_move_1_13] using cert20_component_1_13_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert20_component_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_seen_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_2_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_2_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_0 = cert20_layer_2_0_0 := by
  decide

def cert20_seen_2_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_2_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_2_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_1 = cert20_layer_2_0_1 := by
  decide

def cert20_seen_2_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_2_0_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_2_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_2 = cert20_layer_2_0_2 := by
  decide

def cert20_seen_2_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_2_0_3 : List ChainEdge :=
  []

theorem cert20_layer_2_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_0_3 = cert20_layer_2_0_3 := by
  decide

theorem cert20_component_2_0_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert20_component_2_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 27 cert20_seen_2_0_0 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_0 cert20_layer_2_0_0 26 cert20_layer_2_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 26 cert20_seen_2_0_1 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_1 cert20_layer_2_0_1 25 cert20_layer_2_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 25 cert20_seen_2_0_2 = cert20_component_2_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_2 cert20_layer_2_0_2 24 cert20_layer_2_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 24 cert20_seen_2_0_3 = cert20_component_2_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_0_3 cert20_layer_2_0_3_eq 24

theorem cert20_step_2_0 :
    closedCollarIndexStepBool word fiber20 2 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_0)
    (by decide) (by decide)
    (by simpa [cert20_move_2_0] using cert20_component_2_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_8_0 = cert20_layer_2_8_0 := by
  decide

def cert20_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_2_8_1 : List ChainEdge :=
  []

theorem cert20_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_8_1 = cert20_layer_2_8_1 := by
  decide

theorem cert20_component_2_8_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 27 cert20_seen_2_8_0 = cert20_component_2_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_8_0 cert20_layer_2_8_0 26 cert20_layer_2_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 26 cert20_seen_2_8_1 = cert20_component_2_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_8_1 cert20_layer_2_8_1_eq 26

theorem cert20_step_2_8 :
    closedCollarIndexStepBool word fiber20 2 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_8)
    (by decide) (by decide)
    (by simpa [cert20_move_2_8] using cert20_component_2_8_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_2_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_2_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_14_0 = cert20_layer_2_14_0 := by
  decide

def cert20_seen_2_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_2_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_2_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_14_1 = cert20_layer_2_14_1 := by
  decide

def cert20_seen_2_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_2_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_2_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_14_2 = cert20_layer_2_14_2 := by
  decide

def cert20_seen_2_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_2_14_3 : List ChainEdge :=
  []

theorem cert20_layer_2_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.r LColor.b cert20_seen_2_14_3 = cert20_layer_2_14_3 := by
  decide

theorem cert20_component_2_14_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_2_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 27 cert20_seen_2_14_0 = cert20_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_14_0 cert20_layer_2_14_0 26 cert20_layer_2_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 26 cert20_seen_2_14_1 = cert20_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_14_1 cert20_layer_2_14_1 25 cert20_layer_2_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 25 cert20_seen_2_14_2 = cert20_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_14_2 cert20_layer_2_14_2 24 cert20_layer_2_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.r LColor.b 24 cert20_seen_2_14_3 = cert20_component_2_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.r LColor.b
    cert20_seen_2_14_3 cert20_layer_2_14_3_eq 24

theorem cert20_step_2_14 :
    closedCollarIndexStepBool word fiber20 2 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_14)
    (by decide) (by decide)
    (by simpa [cert20_move_2_14] using cert20_component_2_14_eq)
    (by decide) (by decide) (by decide)

def cert20_move_2_24 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_2_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_2_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_2_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_2_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_0 = cert20_layer_2_24_0 := by
  decide

def cert20_seen_2_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_2_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_2_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_1 = cert20_layer_2_24_1 := by
  decide

def cert20_seen_2_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_2_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_2_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_2 = cert20_layer_2_24_2 := by
  decide

def cert20_seen_2_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_2_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_2_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_3 = cert20_layer_2_24_3 := by
  decide

def cert20_seen_2_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_2_24_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_2_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_4 = cert20_layer_2_24_4 := by
  decide

def cert20_seen_2_24_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_2_24_5 : List ChainEdge :=
  []

theorem cert20_layer_2_24_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 2 [])
      LColor.b LColor.p cert20_seen_2_24_5 = cert20_layer_2_24_5 := by
  decide

theorem cert20_component_2_24_eq :
    closedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_2_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 27 cert20_seen_2_24_0 = cert20_component_2_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_0 cert20_layer_2_24_0 26 cert20_layer_2_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 26 cert20_seen_2_24_1 = cert20_component_2_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_1 cert20_layer_2_24_1 25 cert20_layer_2_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 25 cert20_seen_2_24_2 = cert20_component_2_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_2 cert20_layer_2_24_2 24 cert20_layer_2_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 24 cert20_seen_2_24_3 = cert20_component_2_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_3 cert20_layer_2_24_3 23 cert20_layer_2_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 23 cert20_seen_2_24_4 = cert20_component_2_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_4 cert20_layer_2_24_4 22 cert20_layer_2_24_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 2 [])
      LColor.b LColor.p 22 cert20_seen_2_24_5 = cert20_component_2_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 2 []) LColor.b LColor.p
    cert20_seen_2_24_5 cert20_layer_2_24_5_eq 22

theorem cert20_step_2_24 :
    closedCollarIndexStepBool word fiber20 2 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_2_24)
    (by decide) (by decide)
    (by simpa [cert20_move_2_24] using cert20_component_2_24_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert20_component_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_seen_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_3_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_3_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_0 = cert20_layer_3_1_0 := by
  decide

def cert20_seen_3_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_3_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_3_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_1 = cert20_layer_3_1_1 := by
  decide

def cert20_seen_3_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_3_1_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_3_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_2 = cert20_layer_3_1_2 := by
  decide

def cert20_seen_3_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_3_1_3 : List ChainEdge :=
  []

theorem cert20_layer_3_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_1_3 = cert20_layer_3_1_3 := by
  decide

theorem cert20_component_3_1_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = cert20_component_3_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 27 cert20_seen_3_1_0 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_0 cert20_layer_3_1_0 26 cert20_layer_3_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 26 cert20_seen_3_1_1 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_1 cert20_layer_3_1_1 25 cert20_layer_3_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 25 cert20_seen_3_1_2 = cert20_component_3_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_2 cert20_layer_3_1_2 24 cert20_layer_3_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 24 cert20_seen_3_1_3 = cert20_component_3_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_1_3 cert20_layer_3_1_3_eq 24

theorem cert20_step_3_1 :
    closedCollarIndexStepBool word fiber20 3 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_1)
    (by decide) (by decide)
    (by simpa [cert20_move_3_1] using cert20_component_3_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_9_0 = cert20_layer_3_9_0 := by
  decide

def cert20_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_3_9_1 : List ChainEdge :=
  []

theorem cert20_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_9_1 = cert20_layer_3_9_1 := by
  decide

theorem cert20_component_3_9_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 27 cert20_seen_3_9_0 = cert20_component_3_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_9_0 cert20_layer_3_9_0 26 cert20_layer_3_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 26 cert20_seen_3_9_1 = cert20_component_3_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_9_1 cert20_layer_3_9_1_eq 26

theorem cert20_step_3_9 :
    closedCollarIndexStepBool word fiber20 3 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_9)
    (by decide) (by decide)
    (by simpa [cert20_move_3_9] using cert20_component_3_9_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_3_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_3_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_15_0 = cert20_layer_3_15_0 := by
  decide

def cert20_seen_3_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_3_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_3_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_15_1 = cert20_layer_3_15_1 := by
  decide

def cert20_seen_3_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_3_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_3_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_15_2 = cert20_layer_3_15_2 := by
  decide

def cert20_seen_3_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_3_15_3 : List ChainEdge :=
  []

theorem cert20_layer_3_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.r LColor.b cert20_seen_3_15_3 = cert20_layer_3_15_3 := by
  decide

theorem cert20_component_3_15_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_3_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 27 cert20_seen_3_15_0 = cert20_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_15_0 cert20_layer_3_15_0 26 cert20_layer_3_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 26 cert20_seen_3_15_1 = cert20_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_15_1 cert20_layer_3_15_1 25 cert20_layer_3_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 25 cert20_seen_3_15_2 = cert20_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_15_2 cert20_layer_3_15_2 24 cert20_layer_3_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.r LColor.b 24 cert20_seen_3_15_3 = cert20_component_3_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.r LColor.b
    cert20_seen_3_15_3 cert20_layer_3_15_3_eq 24

theorem cert20_step_3_15 :
    closedCollarIndexStepBool word fiber20 3 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_15)
    (by decide) (by decide)
    (by simpa [cert20_move_3_15] using cert20_component_3_15_eq)
    (by decide) (by decide) (by decide)

def cert20_move_3_25 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_3_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_3_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_3_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_3_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_0 = cert20_layer_3_25_0 := by
  decide

def cert20_seen_3_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_3_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_3_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_1 = cert20_layer_3_25_1 := by
  decide

def cert20_seen_3_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_3_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_3_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_2 = cert20_layer_3_25_2 := by
  decide

def cert20_seen_3_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_3_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_3_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_3 = cert20_layer_3_25_3 := by
  decide

def cert20_seen_3_25_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_3_25_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_3_25_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_4 = cert20_layer_3_25_4 := by
  decide

def cert20_seen_3_25_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_3_25_5 : List ChainEdge :=
  []

theorem cert20_layer_3_25_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 3 [])
      LColor.b LColor.p cert20_seen_3_25_5 = cert20_layer_3_25_5 := by
  decide

theorem cert20_component_3_25_eq :
    closedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_3_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 27 cert20_seen_3_25_0 = cert20_component_3_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_0 cert20_layer_3_25_0 26 cert20_layer_3_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 26 cert20_seen_3_25_1 = cert20_component_3_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_1 cert20_layer_3_25_1 25 cert20_layer_3_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 25 cert20_seen_3_25_2 = cert20_component_3_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_2 cert20_layer_3_25_2 24 cert20_layer_3_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 24 cert20_seen_3_25_3 = cert20_component_3_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_3 cert20_layer_3_25_3 23 cert20_layer_3_25_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 23 cert20_seen_3_25_4 = cert20_component_3_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_4 cert20_layer_3_25_4 22 cert20_layer_3_25_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 3 [])
      LColor.b LColor.p 22 cert20_seen_3_25_5 = cert20_component_3_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 3 []) LColor.b LColor.p
    cert20_seen_3_25_5 cert20_layer_3_25_5_eq 22

theorem cert20_step_3_25 :
    closedCollarIndexStepBool word fiber20 3 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_3_25)
    (by decide) (by decide)
    (by simpa [cert20_move_3_25] using cert20_component_3_25_eq)
    (by decide) (by decide) (by decide)

def cert20_move_4_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert20_component_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_4_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_4_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.p cert20_seen_4_1_0 = cert20_layer_4_1_0 := by
  decide

def cert20_seen_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_4_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_4_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.p cert20_seen_4_1_1 = cert20_layer_4_1_1 := by
  decide

def cert20_seen_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_4_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_4_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.p cert20_seen_4_1_2 = cert20_layer_4_1_2 := by
  decide

def cert20_seen_4_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_4_1_3 : List ChainEdge :=
  []

theorem cert20_layer_4_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.p cert20_seen_4_1_3 = cert20_layer_4_1_3 := by
  decide

theorem cert20_component_4_1_eq :
    closedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert20_component_4_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 4 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.p 27 cert20_seen_4_1_0 = cert20_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.p
    cert20_seen_4_1_0 cert20_layer_4_1_0 26 cert20_layer_4_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.p 26 cert20_seen_4_1_1 = cert20_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.p
    cert20_seen_4_1_1 cert20_layer_4_1_1 25 cert20_layer_4_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.p 25 cert20_seen_4_1_2 = cert20_component_4_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.p
    cert20_seen_4_1_2 cert20_layer_4_1_2 24 cert20_layer_4_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.p 24 cert20_seen_4_1_3 = cert20_component_4_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 4 []) LColor.r LColor.p
    cert20_seen_4_1_3 cert20_layer_4_1_3_eq 24

theorem cert20_step_4_1 :
    closedCollarIndexStepBool word fiber20 4 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_4_1)
    (by decide) (by decide)
    (by simpa [cert20_move_4_1] using cert20_component_4_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_4_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_10_0 = cert20_layer_4_10_0 := by
  decide

def cert20_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_4_10_1 : List ChainEdge :=
  []

theorem cert20_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_10_1 = cert20_layer_4_10_1 := by
  decide

theorem cert20_component_4_10_eq :
    closedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 27 cert20_seen_4_10_0 = cert20_component_4_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_10_0 cert20_layer_4_10_0 26 cert20_layer_4_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 26 cert20_seen_4_10_1 = cert20_component_4_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_10_1 cert20_layer_4_10_1_eq 26

theorem cert20_step_4_10 :
    closedCollarIndexStepBool word fiber20 4 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_4_10)
    (by decide) (by decide)
    (by simpa [cert20_move_4_10] using cert20_component_4_10_eq)
    (by decide) (by decide) (by decide)

def cert20_move_4_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_4_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_4_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_0 = cert20_layer_4_16_0 := by
  decide

def cert20_seen_4_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_4_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_4_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_1 = cert20_layer_4_16_1 := by
  decide

def cert20_seen_4_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_4_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_4_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_2 = cert20_layer_4_16_2 := by
  decide

def cert20_seen_4_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_4_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_4_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_3 = cert20_layer_4_16_3 := by
  decide

def cert20_seen_4_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_4_16_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_4_16_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_4 = cert20_layer_4_16_4 := by
  decide

def cert20_seen_4_16_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_4_16_5 : List ChainEdge :=
  []

theorem cert20_layer_4_16_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.r LColor.b cert20_seen_4_16_5 = cert20_layer_4_16_5 := by
  decide

theorem cert20_component_4_16_eq :
    closedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_4_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 27 cert20_seen_4_16_0 = cert20_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_0 cert20_layer_4_16_0 26 cert20_layer_4_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 26 cert20_seen_4_16_1 = cert20_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_1 cert20_layer_4_16_1 25 cert20_layer_4_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 25 cert20_seen_4_16_2 = cert20_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_2 cert20_layer_4_16_2 24 cert20_layer_4_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 24 cert20_seen_4_16_3 = cert20_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_3 cert20_layer_4_16_3 23 cert20_layer_4_16_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 23 cert20_seen_4_16_4 = cert20_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_4 cert20_layer_4_16_4 22 cert20_layer_4_16_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.r LColor.b 22 cert20_seen_4_16_5 = cert20_component_4_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 4 []) LColor.r LColor.b
    cert20_seen_4_16_5 cert20_layer_4_16_5_eq 22

theorem cert20_step_4_16 :
    closedCollarIndexStepBool word fiber20 4 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_4_16)
    (by decide) (by decide)
    (by simpa [cert20_move_4_16] using cert20_component_4_16_eq)
    (by decide) (by decide) (by decide)

def cert20_move_4_26 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_4_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_4_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_4_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_4_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_26_0 = cert20_layer_4_26_0 := by
  decide

def cert20_seen_4_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_4_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_4_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_26_1 = cert20_layer_4_26_1 := by
  decide

def cert20_seen_4_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_4_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_4_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_26_2 = cert20_layer_4_26_2 := by
  decide

def cert20_seen_4_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_4_26_3 : List ChainEdge :=
  []

theorem cert20_layer_4_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 4 [])
      LColor.b LColor.p cert20_seen_4_26_3 = cert20_layer_4_26_3 := by
  decide

theorem cert20_component_4_26_eq :
    closedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_4_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 27 cert20_seen_4_26_0 = cert20_component_4_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_26_0 cert20_layer_4_26_0 26 cert20_layer_4_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 26 cert20_seen_4_26_1 = cert20_component_4_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_26_1 cert20_layer_4_26_1 25 cert20_layer_4_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 25 cert20_seen_4_26_2 = cert20_component_4_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_26_2 cert20_layer_4_26_2 24 cert20_layer_4_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 4 [])
      LColor.b LColor.p 24 cert20_seen_4_26_3 = cert20_component_4_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 4 []) LColor.b LColor.p
    cert20_seen_4_26_3 cert20_layer_4_26_3_eq 24

theorem cert20_step_4_26 :
    closedCollarIndexStepBool word fiber20 4 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_4_26)
    (by decide) (by decide)
    (by simpa [cert20_move_4_26] using cert20_component_4_26_eq)
    (by decide) (by decide) (by decide)

def cert20_move_5_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert20_component_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_5_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_5_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.p cert20_seen_5_0_0 = cert20_layer_5_0_0 := by
  decide

def cert20_seen_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_5_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_5_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.p cert20_seen_5_0_1 = cert20_layer_5_0_1 := by
  decide

def cert20_seen_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_5_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_5_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.p cert20_seen_5_0_2 = cert20_layer_5_0_2 := by
  decide

def cert20_seen_5_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_5_0_3 : List ChainEdge :=
  []

theorem cert20_layer_5_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.p cert20_seen_5_0_3 = cert20_layer_5_0_3 := by
  decide

theorem cert20_component_5_0_eq :
    closedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = cert20_component_5_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 5 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.p 27 cert20_seen_5_0_0 = cert20_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.p
    cert20_seen_5_0_0 cert20_layer_5_0_0 26 cert20_layer_5_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.p 26 cert20_seen_5_0_1 = cert20_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.p
    cert20_seen_5_0_1 cert20_layer_5_0_1 25 cert20_layer_5_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.p 25 cert20_seen_5_0_2 = cert20_component_5_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.p
    cert20_seen_5_0_2 cert20_layer_5_0_2 24 cert20_layer_5_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.p 24 cert20_seen_5_0_3 = cert20_component_5_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 5 []) LColor.r LColor.p
    cert20_seen_5_0_3 cert20_layer_5_0_3_eq 24

theorem cert20_step_5_0 :
    closedCollarIndexStepBool word fiber20 5 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_5_0)
    (by decide) (by decide)
    (by simpa [cert20_move_5_0] using cert20_component_5_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_5_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_11_0 = cert20_layer_5_11_0 := by
  decide

def cert20_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_5_11_1 : List ChainEdge :=
  []

theorem cert20_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_11_1 = cert20_layer_5_11_1 := by
  decide

theorem cert20_component_5_11_eq :
    closedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 27 cert20_seen_5_11_0 = cert20_component_5_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_11_0 cert20_layer_5_11_0 26 cert20_layer_5_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 26 cert20_seen_5_11_1 = cert20_component_5_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_11_1 cert20_layer_5_11_1_eq 26

theorem cert20_step_5_11 :
    closedCollarIndexStepBool word fiber20 5 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_5_11)
    (by decide) (by decide)
    (by simpa [cert20_move_5_11] using cert20_component_5_11_eq)
    (by decide) (by decide) (by decide)

def cert20_move_5_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_5_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_5_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_0 = cert20_layer_5_17_0 := by
  decide

def cert20_seen_5_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_5_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_5_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_1 = cert20_layer_5_17_1 := by
  decide

def cert20_seen_5_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_5_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_5_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_2 = cert20_layer_5_17_2 := by
  decide

def cert20_seen_5_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_5_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_5_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_3 = cert20_layer_5_17_3 := by
  decide

def cert20_seen_5_17_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_5_17_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_5_17_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_4 = cert20_layer_5_17_4 := by
  decide

def cert20_seen_5_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_5_17_5 : List ChainEdge :=
  []

theorem cert20_layer_5_17_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.r LColor.b cert20_seen_5_17_5 = cert20_layer_5_17_5 := by
  decide

theorem cert20_component_5_17_eq :
    closedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_5_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 27 cert20_seen_5_17_0 = cert20_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_0 cert20_layer_5_17_0 26 cert20_layer_5_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 26 cert20_seen_5_17_1 = cert20_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_1 cert20_layer_5_17_1 25 cert20_layer_5_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 25 cert20_seen_5_17_2 = cert20_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_2 cert20_layer_5_17_2 24 cert20_layer_5_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 24 cert20_seen_5_17_3 = cert20_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_3 cert20_layer_5_17_3 23 cert20_layer_5_17_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 23 cert20_seen_5_17_4 = cert20_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_4 cert20_layer_5_17_4 22 cert20_layer_5_17_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.r LColor.b 22 cert20_seen_5_17_5 = cert20_component_5_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 5 []) LColor.r LColor.b
    cert20_seen_5_17_5 cert20_layer_5_17_5_eq 22

theorem cert20_step_5_17 :
    closedCollarIndexStepBool word fiber20 5 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_5_17)
    (by decide) (by decide)
    (by simpa [cert20_move_5_17] using cert20_component_5_17_eq)
    (by decide) (by decide) (by decide)

def cert20_move_5_27 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_5_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_5_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_5_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_5_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_27_0 = cert20_layer_5_27_0 := by
  decide

def cert20_seen_5_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_5_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_5_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_27_1 = cert20_layer_5_27_1 := by
  decide

def cert20_seen_5_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_5_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_5_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_27_2 = cert20_layer_5_27_2 := by
  decide

def cert20_seen_5_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_5_27_3 : List ChainEdge :=
  []

theorem cert20_layer_5_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 5 [])
      LColor.b LColor.p cert20_seen_5_27_3 = cert20_layer_5_27_3 := by
  decide

theorem cert20_component_5_27_eq :
    closedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_5_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 27 cert20_seen_5_27_0 = cert20_component_5_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_27_0 cert20_layer_5_27_0 26 cert20_layer_5_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 26 cert20_seen_5_27_1 = cert20_component_5_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_27_1 cert20_layer_5_27_1 25 cert20_layer_5_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 25 cert20_seen_5_27_2 = cert20_component_5_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_27_2 cert20_layer_5_27_2 24 cert20_layer_5_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 5 [])
      LColor.b LColor.p 24 cert20_seen_5_27_3 = cert20_component_5_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 5 []) LColor.b LColor.p
    cert20_seen_5_27_3 cert20_layer_5_27_3_eq 24

theorem cert20_step_5_27 :
    closedCollarIndexStepBool word fiber20 5 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_5_27)
    (by decide) (by decide)
    (by simpa [cert20_move_5_27] using cert20_component_5_27_eq)
    (by decide) (by decide) (by decide)

def cert20_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.b LColor.p cert20_seen_6_0_0 = cert20_layer_6_0_0 := by
  decide

def cert20_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_6_0_1 : List ChainEdge :=
  []

theorem cert20_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.b LColor.p cert20_seen_6_0_1 = cert20_layer_6_0_1 := by
  decide

theorem cert20_component_6_0_eq :
    closedCollarComponent word (listGetD fiber20 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.b LColor.p 27 cert20_seen_6_0_0 = cert20_component_6_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 6 []) LColor.b LColor.p
    cert20_seen_6_0_0 cert20_layer_6_0_0 26 cert20_layer_6_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.b LColor.p 26 cert20_seen_6_0_1 = cert20_component_6_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 6 []) LColor.b LColor.p
    cert20_seen_6_0_1 cert20_layer_6_0_1_eq 26

theorem cert20_step_6_0 :
    closedCollarIndexStepBool word fiber20 6 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_6_0)
    (by decide) (by decide)
    (by simpa [cert20_move_6_0] using cert20_component_6_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_6_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_6_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_6_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.r LColor.b cert20_seen_6_18_0 = cert20_layer_6_18_0 := by
  decide

def cert20_seen_6_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_6_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_6_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.r LColor.b cert20_seen_6_18_1 = cert20_layer_6_18_1 := by
  decide

def cert20_seen_6_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_6_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_6_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.r LColor.b cert20_seen_6_18_2 = cert20_layer_6_18_2 := by
  decide

def cert20_seen_6_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_6_18_3 : List ChainEdge :=
  []

theorem cert20_layer_6_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 6 [])
      LColor.r LColor.b cert20_seen_6_18_3 = cert20_layer_6_18_3 := by
  decide

theorem cert20_component_6_18_eq :
    closedCollarComponent word (listGetD fiber20 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_6_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.r LColor.b 27 cert20_seen_6_18_0 = cert20_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 6 []) LColor.r LColor.b
    cert20_seen_6_18_0 cert20_layer_6_18_0 26 cert20_layer_6_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.r LColor.b 26 cert20_seen_6_18_1 = cert20_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 6 []) LColor.r LColor.b
    cert20_seen_6_18_1 cert20_layer_6_18_1 25 cert20_layer_6_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.r LColor.b 25 cert20_seen_6_18_2 = cert20_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 6 []) LColor.r LColor.b
    cert20_seen_6_18_2 cert20_layer_6_18_2 24 cert20_layer_6_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 6 [])
      LColor.r LColor.b 24 cert20_seen_6_18_3 = cert20_component_6_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 6 []) LColor.r LColor.b
    cert20_seen_6_18_3 cert20_layer_6_18_3_eq 24

theorem cert20_step_6_18 :
    closedCollarIndexStepBool word fiber20 6 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_6_18)
    (by decide) (by decide)
    (by simpa [cert20_move_6_18] using cert20_component_6_18_eq)
    (by decide) (by decide) (by decide)

def cert20_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.b LColor.p cert20_seen_7_1_0 = cert20_layer_7_1_0 := by
  decide

def cert20_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_7_1_1 : List ChainEdge :=
  []

theorem cert20_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.b LColor.p cert20_seen_7_1_1 = cert20_layer_7_1_1 := by
  decide

theorem cert20_component_7_1_eq :
    closedCollarComponent word (listGetD fiber20 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.b LColor.p 27 cert20_seen_7_1_0 = cert20_component_7_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 7 []) LColor.b LColor.p
    cert20_seen_7_1_0 cert20_layer_7_1_0 26 cert20_layer_7_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.b LColor.p 26 cert20_seen_7_1_1 = cert20_component_7_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 7 []) LColor.b LColor.p
    cert20_seen_7_1_1 cert20_layer_7_1_1_eq 26

theorem cert20_step_7_1 :
    closedCollarIndexStepBool word fiber20 7 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_7_1)
    (by decide) (by decide)
    (by simpa [cert20_move_7_1] using cert20_component_7_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_7_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_7_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_7_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.r LColor.b cert20_seen_7_19_0 = cert20_layer_7_19_0 := by
  decide

def cert20_seen_7_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_7_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_7_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.r LColor.b cert20_seen_7_19_1 = cert20_layer_7_19_1 := by
  decide

def cert20_seen_7_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_7_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_7_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.r LColor.b cert20_seen_7_19_2 = cert20_layer_7_19_2 := by
  decide

def cert20_seen_7_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_7_19_3 : List ChainEdge :=
  []

theorem cert20_layer_7_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 7 [])
      LColor.r LColor.b cert20_seen_7_19_3 = cert20_layer_7_19_3 := by
  decide

theorem cert20_component_7_19_eq :
    closedCollarComponent word (listGetD fiber20 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_7_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.r LColor.b 27 cert20_seen_7_19_0 = cert20_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 7 []) LColor.r LColor.b
    cert20_seen_7_19_0 cert20_layer_7_19_0 26 cert20_layer_7_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.r LColor.b 26 cert20_seen_7_19_1 = cert20_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 7 []) LColor.r LColor.b
    cert20_seen_7_19_1 cert20_layer_7_19_1 25 cert20_layer_7_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.r LColor.b 25 cert20_seen_7_19_2 = cert20_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 7 []) LColor.r LColor.b
    cert20_seen_7_19_2 cert20_layer_7_19_2 24 cert20_layer_7_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 7 [])
      LColor.r LColor.b 24 cert20_seen_7_19_3 = cert20_component_7_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 7 []) LColor.r LColor.b
    cert20_seen_7_19_3 cert20_layer_7_19_3_eq 24

theorem cert20_step_7_19 :
    closedCollarIndexStepBool word fiber20 7 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_7_19)
    (by decide) (by decide)
    (by simpa [cert20_move_7_19] using cert20_component_7_19_eq)
    (by decide) (by decide) (by decide)

def cert20_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_2_0 = cert20_layer_8_2_0 := by
  decide

def cert20_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_8_2_1 : List ChainEdge :=
  []

theorem cert20_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_2_1 = cert20_layer_8_2_1 := by
  decide

theorem cert20_component_8_2_eq :
    closedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 27 cert20_seen_8_2_0 = cert20_component_8_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_2_0 cert20_layer_8_2_0 26 cert20_layer_8_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 26 cert20_seen_8_2_1 = cert20_component_8_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_2_1 cert20_layer_8_2_1_eq 26

theorem cert20_step_8_2 :
    closedCollarIndexStepBool word fiber20 8 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_8_2)
    (by decide) (by decide)
    (by simpa [cert20_move_8_2] using cert20_component_8_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_8_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_8_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_8_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.r LColor.b cert20_seen_8_20_0 = cert20_layer_8_20_0 := by
  decide

def cert20_seen_8_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_8_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_8_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.r LColor.b cert20_seen_8_20_1 = cert20_layer_8_20_1 := by
  decide

def cert20_seen_8_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_8_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_8_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.r LColor.b cert20_seen_8_20_2 = cert20_layer_8_20_2 := by
  decide

def cert20_seen_8_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_8_20_3 : List ChainEdge :=
  []

theorem cert20_layer_8_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.r LColor.b cert20_seen_8_20_3 = cert20_layer_8_20_3 := by
  decide

theorem cert20_component_8_20_eq :
    closedCollarComponent word (listGetD fiber20 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_8_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.r LColor.b 27 cert20_seen_8_20_0 = cert20_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.r LColor.b
    cert20_seen_8_20_0 cert20_layer_8_20_0 26 cert20_layer_8_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.r LColor.b 26 cert20_seen_8_20_1 = cert20_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.r LColor.b
    cert20_seen_8_20_1 cert20_layer_8_20_1 25 cert20_layer_8_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.r LColor.b 25 cert20_seen_8_20_2 = cert20_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.r LColor.b
    cert20_seen_8_20_2 cert20_layer_8_20_2 24 cert20_layer_8_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.r LColor.b 24 cert20_seen_8_20_3 = cert20_component_8_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 8 []) LColor.r LColor.b
    cert20_seen_8_20_3 cert20_layer_8_20_3_eq 24

theorem cert20_step_8_20 :
    closedCollarIndexStepBool word fiber20 8 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_8_20)
    (by decide) (by decide)
    (by simpa [cert20_move_8_20] using cert20_component_8_20_eq)
    (by decide) (by decide) (by decide)

def cert20_move_8_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_8_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_8_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_8_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_8_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_0 = cert20_layer_8_28_0 := by
  decide

def cert20_seen_8_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_8_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_8_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_1 = cert20_layer_8_28_1 := by
  decide

def cert20_seen_8_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_8_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_8_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_2 = cert20_layer_8_28_2 := by
  decide

def cert20_seen_8_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_8_28_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_8_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_3 = cert20_layer_8_28_3 := by
  decide

def cert20_seen_8_28_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_8_28_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_8_28_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_4 = cert20_layer_8_28_4 := by
  decide

def cert20_seen_8_28_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_8_28_5 : List ChainEdge :=
  []

theorem cert20_layer_8_28_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 8 [])
      LColor.b LColor.p cert20_seen_8_28_5 = cert20_layer_8_28_5 := by
  decide

theorem cert20_component_8_28_eq :
    closedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_8_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 27 cert20_seen_8_28_0 = cert20_component_8_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_0 cert20_layer_8_28_0 26 cert20_layer_8_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 26 cert20_seen_8_28_1 = cert20_component_8_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_1 cert20_layer_8_28_1 25 cert20_layer_8_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 25 cert20_seen_8_28_2 = cert20_component_8_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_2 cert20_layer_8_28_2 24 cert20_layer_8_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 24 cert20_seen_8_28_3 = cert20_component_8_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_3 cert20_layer_8_28_3 23 cert20_layer_8_28_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 23 cert20_seen_8_28_4 = cert20_component_8_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_4 cert20_layer_8_28_4 22 cert20_layer_8_28_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 8 [])
      LColor.b LColor.p 22 cert20_seen_8_28_5 = cert20_component_8_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 8 []) LColor.b LColor.p
    cert20_seen_8_28_5 cert20_layer_8_28_5_eq 22

theorem cert20_step_8_28 :
    closedCollarIndexStepBool word fiber20 8 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_8_28)
    (by decide) (by decide)
    (by simpa [cert20_move_8_28] using cert20_component_8_28_eq)
    (by decide) (by decide) (by decide)

def cert20_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_3_0 = cert20_layer_9_3_0 := by
  decide

def cert20_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_9_3_1 : List ChainEdge :=
  []

theorem cert20_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_3_1 = cert20_layer_9_3_1 := by
  decide

theorem cert20_component_9_3_eq :
    closedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 27 cert20_seen_9_3_0 = cert20_component_9_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_3_0 cert20_layer_9_3_0 26 cert20_layer_9_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 26 cert20_seen_9_3_1 = cert20_component_9_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_3_1 cert20_layer_9_3_1_eq 26

theorem cert20_step_9_3 :
    closedCollarIndexStepBool word fiber20 9 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_9_3)
    (by decide) (by decide)
    (by simpa [cert20_move_9_3] using cert20_component_9_3_eq)
    (by decide) (by decide) (by decide)

def cert20_move_9_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_9_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_9_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.r LColor.b cert20_seen_9_21_0 = cert20_layer_9_21_0 := by
  decide

def cert20_seen_9_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_9_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_9_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.r LColor.b cert20_seen_9_21_1 = cert20_layer_9_21_1 := by
  decide

def cert20_seen_9_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_9_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_9_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.r LColor.b cert20_seen_9_21_2 = cert20_layer_9_21_2 := by
  decide

def cert20_seen_9_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_9_21_3 : List ChainEdge :=
  []

theorem cert20_layer_9_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.r LColor.b cert20_seen_9_21_3 = cert20_layer_9_21_3 := by
  decide

theorem cert20_component_9_21_eq :
    closedCollarComponent word (listGetD fiber20 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_9_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.r LColor.b 27 cert20_seen_9_21_0 = cert20_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.r LColor.b
    cert20_seen_9_21_0 cert20_layer_9_21_0 26 cert20_layer_9_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.r LColor.b 26 cert20_seen_9_21_1 = cert20_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.r LColor.b
    cert20_seen_9_21_1 cert20_layer_9_21_1 25 cert20_layer_9_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.r LColor.b 25 cert20_seen_9_21_2 = cert20_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.r LColor.b
    cert20_seen_9_21_2 cert20_layer_9_21_2 24 cert20_layer_9_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.r LColor.b 24 cert20_seen_9_21_3 = cert20_component_9_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 9 []) LColor.r LColor.b
    cert20_seen_9_21_3 cert20_layer_9_21_3_eq 24

theorem cert20_step_9_21 :
    closedCollarIndexStepBool word fiber20 9 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_9_21)
    (by decide) (by decide)
    (by simpa [cert20_move_9_21] using cert20_component_9_21_eq)
    (by decide) (by decide) (by decide)

def cert20_move_9_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_9_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_9_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_9_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_9_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_0 = cert20_layer_9_29_0 := by
  decide

def cert20_seen_9_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_9_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_9_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_1 = cert20_layer_9_29_1 := by
  decide

def cert20_seen_9_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_9_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_9_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_2 = cert20_layer_9_29_2 := by
  decide

def cert20_seen_9_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_9_29_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_9_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_3 = cert20_layer_9_29_3 := by
  decide

def cert20_seen_9_29_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_9_29_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_9_29_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_4 = cert20_layer_9_29_4 := by
  decide

def cert20_seen_9_29_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_9_29_5 : List ChainEdge :=
  []

theorem cert20_layer_9_29_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 9 [])
      LColor.b LColor.p cert20_seen_9_29_5 = cert20_layer_9_29_5 := by
  decide

theorem cert20_component_9_29_eq :
    closedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_9_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 27 cert20_seen_9_29_0 = cert20_component_9_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_0 cert20_layer_9_29_0 26 cert20_layer_9_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 26 cert20_seen_9_29_1 = cert20_component_9_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_1 cert20_layer_9_29_1 25 cert20_layer_9_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 25 cert20_seen_9_29_2 = cert20_component_9_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_2 cert20_layer_9_29_2 24 cert20_layer_9_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 24 cert20_seen_9_29_3 = cert20_component_9_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_3 cert20_layer_9_29_3 23 cert20_layer_9_29_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 23 cert20_seen_9_29_4 = cert20_component_9_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_4 cert20_layer_9_29_4 22 cert20_layer_9_29_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 9 [])
      LColor.b LColor.p 22 cert20_seen_9_29_5 = cert20_component_9_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 9 []) LColor.b LColor.p
    cert20_seen_9_29_5 cert20_layer_9_29_5_eq 22

theorem cert20_step_9_29 :
    closedCollarIndexStepBool word fiber20 9 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_9_29)
    (by decide) (by decide)
    (by simpa [cert20_move_9_29] using cert20_component_9_29_eq)
    (by decide) (by decide) (by decide)

def cert20_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_4_0 = cert20_layer_10_4_0 := by
  decide

def cert20_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_10_4_1 : List ChainEdge :=
  []

theorem cert20_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_4_1 = cert20_layer_10_4_1 := by
  decide

theorem cert20_component_10_4_eq :
    closedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 27 cert20_seen_10_4_0 = cert20_component_10_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_4_0 cert20_layer_10_4_0 26 cert20_layer_10_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 26 cert20_seen_10_4_1 = cert20_component_10_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_4_1 cert20_layer_10_4_1_eq 26

theorem cert20_step_10_4 :
    closedCollarIndexStepBool word fiber20 10 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_10_4)
    (by decide) (by decide)
    (by simpa [cert20_move_10_4] using cert20_component_10_4_eq)
    (by decide) (by decide) (by decide)

def cert20_move_10_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_10_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_10_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_0 = cert20_layer_10_22_0 := by
  decide

def cert20_seen_10_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_10_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_10_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_1 = cert20_layer_10_22_1 := by
  decide

def cert20_seen_10_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_10_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_10_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_2 = cert20_layer_10_22_2 := by
  decide

def cert20_seen_10_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_10_22_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_10_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_3 = cert20_layer_10_22_3 := by
  decide

def cert20_seen_10_22_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_10_22_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_10_22_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_4 = cert20_layer_10_22_4 := by
  decide

def cert20_seen_10_22_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_10_22_5 : List ChainEdge :=
  []

theorem cert20_layer_10_22_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.r LColor.b cert20_seen_10_22_5 = cert20_layer_10_22_5 := by
  decide

theorem cert20_component_10_22_eq :
    closedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_10_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 27 cert20_seen_10_22_0 = cert20_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_0 cert20_layer_10_22_0 26 cert20_layer_10_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 26 cert20_seen_10_22_1 = cert20_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_1 cert20_layer_10_22_1 25 cert20_layer_10_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 25 cert20_seen_10_22_2 = cert20_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_2 cert20_layer_10_22_2 24 cert20_layer_10_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 24 cert20_seen_10_22_3 = cert20_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_3 cert20_layer_10_22_3 23 cert20_layer_10_22_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 23 cert20_seen_10_22_4 = cert20_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_4 cert20_layer_10_22_4 22 cert20_layer_10_22_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.r LColor.b 22 cert20_seen_10_22_5 = cert20_component_10_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 10 []) LColor.r LColor.b
    cert20_seen_10_22_5 cert20_layer_10_22_5_eq 22

theorem cert20_step_10_22 :
    closedCollarIndexStepBool word fiber20 10 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_10_22)
    (by decide) (by decide)
    (by simpa [cert20_move_10_22] using cert20_component_10_22_eq)
    (by decide) (by decide) (by decide)

def cert20_move_10_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_10_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_10_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_10_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_10_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_30_0 = cert20_layer_10_30_0 := by
  decide

def cert20_seen_10_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_10_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_10_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_30_1 = cert20_layer_10_30_1 := by
  decide

def cert20_seen_10_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_10_30_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_10_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_30_2 = cert20_layer_10_30_2 := by
  decide

def cert20_seen_10_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_10_30_3 : List ChainEdge :=
  []

theorem cert20_layer_10_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 10 [])
      LColor.b LColor.p cert20_seen_10_30_3 = cert20_layer_10_30_3 := by
  decide

theorem cert20_component_10_30_eq :
    closedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_10_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 27 cert20_seen_10_30_0 = cert20_component_10_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_30_0 cert20_layer_10_30_0 26 cert20_layer_10_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 26 cert20_seen_10_30_1 = cert20_component_10_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_30_1 cert20_layer_10_30_1 25 cert20_layer_10_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 25 cert20_seen_10_30_2 = cert20_component_10_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_30_2 cert20_layer_10_30_2 24 cert20_layer_10_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 10 [])
      LColor.b LColor.p 24 cert20_seen_10_30_3 = cert20_component_10_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 10 []) LColor.b LColor.p
    cert20_seen_10_30_3 cert20_layer_10_30_3_eq 24

theorem cert20_step_10_30 :
    closedCollarIndexStepBool word fiber20 10 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_10_30)
    (by decide) (by decide)
    (by simpa [cert20_move_10_30] using cert20_component_10_30_eq)
    (by decide) (by decide) (by decide)

def cert20_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert20_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert20_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_5_0 = cert20_layer_11_5_0 := by
  decide

def cert20_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_11_5_1 : List ChainEdge :=
  []

theorem cert20_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_5_1 = cert20_layer_11_5_1 := by
  decide

theorem cert20_component_11_5_eq :
    closedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert20_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 27 cert20_seen_11_5_0 = cert20_component_11_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_5_0 cert20_layer_11_5_0 26 cert20_layer_11_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 26 cert20_seen_11_5_1 = cert20_component_11_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_5_1 cert20_layer_11_5_1_eq 26

theorem cert20_step_11_5 :
    closedCollarIndexStepBool word fiber20 11 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_11_5)
    (by decide) (by decide)
    (by simpa [cert20_move_11_5] using cert20_component_11_5_eq)
    (by decide) (by decide) (by decide)

def cert20_move_11_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_11_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_11_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_0 = cert20_layer_11_23_0 := by
  decide

def cert20_seen_11_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_11_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_11_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_1 = cert20_layer_11_23_1 := by
  decide

def cert20_seen_11_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_11_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_11_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_2 = cert20_layer_11_23_2 := by
  decide

def cert20_seen_11_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_11_23_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_11_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_3 = cert20_layer_11_23_3 := by
  decide

def cert20_seen_11_23_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_11_23_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_11_23_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_4 = cert20_layer_11_23_4 := by
  decide

def cert20_seen_11_23_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_11_23_5 : List ChainEdge :=
  []

theorem cert20_layer_11_23_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.r LColor.b cert20_seen_11_23_5 = cert20_layer_11_23_5 := by
  decide

theorem cert20_component_11_23_eq :
    closedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_11_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 27 cert20_seen_11_23_0 = cert20_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_0 cert20_layer_11_23_0 26 cert20_layer_11_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 26 cert20_seen_11_23_1 = cert20_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_1 cert20_layer_11_23_1 25 cert20_layer_11_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 25 cert20_seen_11_23_2 = cert20_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_2 cert20_layer_11_23_2 24 cert20_layer_11_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 24 cert20_seen_11_23_3 = cert20_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_3 cert20_layer_11_23_3 23 cert20_layer_11_23_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 23 cert20_seen_11_23_4 = cert20_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_4 cert20_layer_11_23_4 22 cert20_layer_11_23_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.r LColor.b 22 cert20_seen_11_23_5 = cert20_component_11_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 11 []) LColor.r LColor.b
    cert20_seen_11_23_5 cert20_layer_11_23_5_eq 22

theorem cert20_step_11_23 :
    closedCollarIndexStepBool word fiber20 11 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_11_23)
    (by decide) (by decide)
    (by simpa [cert20_move_11_23] using cert20_component_11_23_eq)
    (by decide) (by decide) (by decide)

def cert20_move_11_31 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_11_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_11_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_11_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_11_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_31_0 = cert20_layer_11_31_0 := by
  decide

def cert20_seen_11_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_11_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_11_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_31_1 = cert20_layer_11_31_1 := by
  decide

def cert20_seen_11_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_11_31_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_11_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_31_2 = cert20_layer_11_31_2 := by
  decide

def cert20_seen_11_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_11_31_3 : List ChainEdge :=
  []

theorem cert20_layer_11_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 11 [])
      LColor.b LColor.p cert20_seen_11_31_3 = cert20_layer_11_31_3 := by
  decide

theorem cert20_component_11_31_eq :
    closedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_11_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 27 cert20_seen_11_31_0 = cert20_component_11_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_31_0 cert20_layer_11_31_0 26 cert20_layer_11_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 26 cert20_seen_11_31_1 = cert20_component_11_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_31_1 cert20_layer_11_31_1 25 cert20_layer_11_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 25 cert20_seen_11_31_2 = cert20_component_11_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_31_2 cert20_layer_11_31_2 24 cert20_layer_11_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 11 [])
      LColor.b LColor.p 24 cert20_seen_11_31_3 = cert20_component_11_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 11 []) LColor.b LColor.p
    cert20_seen_11_31_3 cert20_layer_11_31_3_eq 24

theorem cert20_step_11_31 :
    closedCollarIndexStepBool word fiber20 11 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_11_31)
    (by decide) (by decide)
    (by simpa [cert20_move_11_31] using cert20_component_11_31_eq)
    (by decide) (by decide) (by decide)

def cert20_move_12_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_12_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.r LColor.b cert20_seen_12_0_0 = cert20_layer_12_0_0 := by
  decide

def cert20_seen_12_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_12_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_12_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.r LColor.b cert20_seen_12_0_1 = cert20_layer_12_0_1 := by
  decide

def cert20_seen_12_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_12_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_12_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.r LColor.b cert20_seen_12_0_2 = cert20_layer_12_0_2 := by
  decide

def cert20_seen_12_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_12_0_3 : List ChainEdge :=
  []

theorem cert20_layer_12_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.r LColor.b cert20_seen_12_0_3 = cert20_layer_12_0_3 := by
  decide

theorem cert20_component_12_0_eq :
    closedCollarComponent word (listGetD fiber20 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_12_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.r LColor.b 27 cert20_seen_12_0_0 = cert20_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.r LColor.b
    cert20_seen_12_0_0 cert20_layer_12_0_0 26 cert20_layer_12_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.r LColor.b 26 cert20_seen_12_0_1 = cert20_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.r LColor.b
    cert20_seen_12_0_1 cert20_layer_12_0_1 25 cert20_layer_12_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.r LColor.b 25 cert20_seen_12_0_2 = cert20_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.r LColor.b
    cert20_seen_12_0_2 cert20_layer_12_0_2 24 cert20_layer_12_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.r LColor.b 24 cert20_seen_12_0_3 = cert20_component_12_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 12 []) LColor.r LColor.b
    cert20_seen_12_0_3 cert20_layer_12_0_3_eq 24

theorem cert20_step_12_0 :
    closedCollarIndexStepBool word fiber20 12 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_12_0)
    (by decide) (by decide)
    (by simpa [cert20_move_12_0] using cert20_component_12_0_eq)
    (by decide) (by decide) (by decide)

def cert20_move_12_32 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_12_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_12_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_12_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_12_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.b LColor.p cert20_seen_12_32_0 = cert20_layer_12_32_0 := by
  decide

def cert20_seen_12_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_12_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_12_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.b LColor.p cert20_seen_12_32_1 = cert20_layer_12_32_1 := by
  decide

def cert20_seen_12_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_12_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_12_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.b LColor.p cert20_seen_12_32_2 = cert20_layer_12_32_2 := by
  decide

def cert20_seen_12_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_12_32_3 : List ChainEdge :=
  []

theorem cert20_layer_12_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 12 [])
      LColor.b LColor.p cert20_seen_12_32_3 = cert20_layer_12_32_3 := by
  decide

theorem cert20_component_12_32_eq :
    closedCollarComponent word (listGetD fiber20 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_12_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 12 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.b LColor.p 27 cert20_seen_12_32_0 = cert20_component_12_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.b LColor.p
    cert20_seen_12_32_0 cert20_layer_12_32_0 26 cert20_layer_12_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.b LColor.p 26 cert20_seen_12_32_1 = cert20_component_12_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.b LColor.p
    cert20_seen_12_32_1 cert20_layer_12_32_1 25 cert20_layer_12_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.b LColor.p 25 cert20_seen_12_32_2 = cert20_component_12_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 12 []) LColor.b LColor.p
    cert20_seen_12_32_2 cert20_layer_12_32_2 24 cert20_layer_12_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 12 [])
      LColor.b LColor.p 24 cert20_seen_12_32_3 = cert20_component_12_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 12 []) LColor.b LColor.p
    cert20_seen_12_32_3 cert20_layer_12_32_3_eq 24

theorem cert20_step_12_32 :
    closedCollarIndexStepBool word fiber20 12 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_12_32)
    (by decide) (by decide)
    (by simpa [cert20_move_12_32] using cert20_component_12_32_eq)
    (by decide) (by decide) (by decide)

def cert20_move_13_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_13_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.r LColor.b cert20_seen_13_1_0 = cert20_layer_13_1_0 := by
  decide

def cert20_seen_13_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_13_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_13_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.r LColor.b cert20_seen_13_1_1 = cert20_layer_13_1_1 := by
  decide

def cert20_seen_13_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_13_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_13_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.r LColor.b cert20_seen_13_1_2 = cert20_layer_13_1_2 := by
  decide

def cert20_seen_13_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_13_1_3 : List ChainEdge :=
  []

theorem cert20_layer_13_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.r LColor.b cert20_seen_13_1_3 = cert20_layer_13_1_3 := by
  decide

theorem cert20_component_13_1_eq :
    closedCollarComponent word (listGetD fiber20 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_13_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.r LColor.b 27 cert20_seen_13_1_0 = cert20_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.r LColor.b
    cert20_seen_13_1_0 cert20_layer_13_1_0 26 cert20_layer_13_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.r LColor.b 26 cert20_seen_13_1_1 = cert20_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.r LColor.b
    cert20_seen_13_1_1 cert20_layer_13_1_1 25 cert20_layer_13_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.r LColor.b 25 cert20_seen_13_1_2 = cert20_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.r LColor.b
    cert20_seen_13_1_2 cert20_layer_13_1_2 24 cert20_layer_13_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.r LColor.b 24 cert20_seen_13_1_3 = cert20_component_13_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 13 []) LColor.r LColor.b
    cert20_seen_13_1_3 cert20_layer_13_1_3_eq 24

theorem cert20_step_13_1 :
    closedCollarIndexStepBool word fiber20 13 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_13_1)
    (by decide) (by decide)
    (by simpa [cert20_move_13_1] using cert20_component_13_1_eq)
    (by decide) (by decide) (by decide)

def cert20_move_13_33 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_13_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_13_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_13_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_13_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.b LColor.p cert20_seen_13_33_0 = cert20_layer_13_33_0 := by
  decide

def cert20_seen_13_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_13_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_13_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.b LColor.p cert20_seen_13_33_1 = cert20_layer_13_33_1 := by
  decide

def cert20_seen_13_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_13_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_13_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.b LColor.p cert20_seen_13_33_2 = cert20_layer_13_33_2 := by
  decide

def cert20_seen_13_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_13_33_3 : List ChainEdge :=
  []

theorem cert20_layer_13_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 13 [])
      LColor.b LColor.p cert20_seen_13_33_3 = cert20_layer_13_33_3 := by
  decide

theorem cert20_component_13_33_eq :
    closedCollarComponent word (listGetD fiber20 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_13_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 13 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.b LColor.p 27 cert20_seen_13_33_0 = cert20_component_13_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.b LColor.p
    cert20_seen_13_33_0 cert20_layer_13_33_0 26 cert20_layer_13_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.b LColor.p 26 cert20_seen_13_33_1 = cert20_component_13_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.b LColor.p
    cert20_seen_13_33_1 cert20_layer_13_33_1 25 cert20_layer_13_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.b LColor.p 25 cert20_seen_13_33_2 = cert20_component_13_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 13 []) LColor.b LColor.p
    cert20_seen_13_33_2 cert20_layer_13_33_2 24 cert20_layer_13_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 13 [])
      LColor.b LColor.p 24 cert20_seen_13_33_3 = cert20_component_13_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 13 []) LColor.b LColor.p
    cert20_seen_13_33_3 cert20_layer_13_33_3_eq 24

theorem cert20_step_13_33 :
    closedCollarIndexStepBool word fiber20 13 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_13_33)
    (by decide) (by decide)
    (by simpa [cert20_move_13_33] using cert20_component_13_33_eq)
    (by decide) (by decide) (by decide)

def cert20_move_14_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_14_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.r LColor.b cert20_seen_14_2_0 = cert20_layer_14_2_0 := by
  decide

def cert20_seen_14_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_14_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_14_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.r LColor.b cert20_seen_14_2_1 = cert20_layer_14_2_1 := by
  decide

def cert20_seen_14_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_14_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_14_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.r LColor.b cert20_seen_14_2_2 = cert20_layer_14_2_2 := by
  decide

def cert20_seen_14_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_14_2_3 : List ChainEdge :=
  []

theorem cert20_layer_14_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.r LColor.b cert20_seen_14_2_3 = cert20_layer_14_2_3 := by
  decide

theorem cert20_component_14_2_eq :
    closedCollarComponent word (listGetD fiber20 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_14_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.r LColor.b 27 cert20_seen_14_2_0 = cert20_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.r LColor.b
    cert20_seen_14_2_0 cert20_layer_14_2_0 26 cert20_layer_14_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.r LColor.b 26 cert20_seen_14_2_1 = cert20_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.r LColor.b
    cert20_seen_14_2_1 cert20_layer_14_2_1 25 cert20_layer_14_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.r LColor.b 25 cert20_seen_14_2_2 = cert20_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.r LColor.b
    cert20_seen_14_2_2 cert20_layer_14_2_2 24 cert20_layer_14_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.r LColor.b 24 cert20_seen_14_2_3 = cert20_component_14_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 14 []) LColor.r LColor.b
    cert20_seen_14_2_3 cert20_layer_14_2_3_eq 24

theorem cert20_step_14_2 :
    closedCollarIndexStepBool word fiber20 14 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_14_2)
    (by decide) (by decide)
    (by simpa [cert20_move_14_2] using cert20_component_14_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_14_34 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_14_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_14_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_14_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_14_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.b LColor.p cert20_seen_14_34_0 = cert20_layer_14_34_0 := by
  decide

def cert20_seen_14_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_14_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_14_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.b LColor.p cert20_seen_14_34_1 = cert20_layer_14_34_1 := by
  decide

def cert20_seen_14_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_14_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_14_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.b LColor.p cert20_seen_14_34_2 = cert20_layer_14_34_2 := by
  decide

def cert20_seen_14_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_14_34_3 : List ChainEdge :=
  []

theorem cert20_layer_14_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 14 [])
      LColor.b LColor.p cert20_seen_14_34_3 = cert20_layer_14_34_3 := by
  decide

theorem cert20_component_14_34_eq :
    closedCollarComponent word (listGetD fiber20 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_14_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 14 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.b LColor.p 27 cert20_seen_14_34_0 = cert20_component_14_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.b LColor.p
    cert20_seen_14_34_0 cert20_layer_14_34_0 26 cert20_layer_14_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.b LColor.p 26 cert20_seen_14_34_1 = cert20_component_14_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.b LColor.p
    cert20_seen_14_34_1 cert20_layer_14_34_1 25 cert20_layer_14_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.b LColor.p 25 cert20_seen_14_34_2 = cert20_component_14_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 14 []) LColor.b LColor.p
    cert20_seen_14_34_2 cert20_layer_14_34_2 24 cert20_layer_14_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 14 [])
      LColor.b LColor.p 24 cert20_seen_14_34_3 = cert20_component_14_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 14 []) LColor.b LColor.p
    cert20_seen_14_34_3 cert20_layer_14_34_3_eq 24

theorem cert20_step_14_34 :
    closedCollarIndexStepBool word fiber20 14 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_14_34)
    (by decide) (by decide)
    (by simpa [cert20_move_14_34] using cert20_component_14_34_eq)
    (by decide) (by decide) (by decide)

def cert20_move_15_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_15_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.r LColor.b cert20_seen_15_3_0 = cert20_layer_15_3_0 := by
  decide

def cert20_seen_15_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_15_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_15_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.r LColor.b cert20_seen_15_3_1 = cert20_layer_15_3_1 := by
  decide

def cert20_seen_15_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_15_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_15_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.r LColor.b cert20_seen_15_3_2 = cert20_layer_15_3_2 := by
  decide

def cert20_seen_15_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_15_3_3 : List ChainEdge :=
  []

theorem cert20_layer_15_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.r LColor.b cert20_seen_15_3_3 = cert20_layer_15_3_3 := by
  decide

theorem cert20_component_15_3_eq :
    closedCollarComponent word (listGetD fiber20 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_15_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.r LColor.b 27 cert20_seen_15_3_0 = cert20_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.r LColor.b
    cert20_seen_15_3_0 cert20_layer_15_3_0 26 cert20_layer_15_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.r LColor.b 26 cert20_seen_15_3_1 = cert20_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.r LColor.b
    cert20_seen_15_3_1 cert20_layer_15_3_1 25 cert20_layer_15_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.r LColor.b 25 cert20_seen_15_3_2 = cert20_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.r LColor.b
    cert20_seen_15_3_2 cert20_layer_15_3_2 24 cert20_layer_15_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.r LColor.b 24 cert20_seen_15_3_3 = cert20_component_15_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 15 []) LColor.r LColor.b
    cert20_seen_15_3_3 cert20_layer_15_3_3_eq 24

theorem cert20_step_15_3 :
    closedCollarIndexStepBool word fiber20 15 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_15_3)
    (by decide) (by decide)
    (by simpa [cert20_move_15_3] using cert20_component_15_3_eq)
    (by decide) (by decide) (by decide)

def cert20_move_15_35 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_15_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_15_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_15_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_15_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.b LColor.p cert20_seen_15_35_0 = cert20_layer_15_35_0 := by
  decide

def cert20_seen_15_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_15_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_15_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.b LColor.p cert20_seen_15_35_1 = cert20_layer_15_35_1 := by
  decide

def cert20_seen_15_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_15_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_15_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.b LColor.p cert20_seen_15_35_2 = cert20_layer_15_35_2 := by
  decide

def cert20_seen_15_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_15_35_3 : List ChainEdge :=
  []

theorem cert20_layer_15_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 15 [])
      LColor.b LColor.p cert20_seen_15_35_3 = cert20_layer_15_35_3 := by
  decide

theorem cert20_component_15_35_eq :
    closedCollarComponent word (listGetD fiber20 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_15_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 15 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.b LColor.p 27 cert20_seen_15_35_0 = cert20_component_15_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.b LColor.p
    cert20_seen_15_35_0 cert20_layer_15_35_0 26 cert20_layer_15_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.b LColor.p 26 cert20_seen_15_35_1 = cert20_component_15_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.b LColor.p
    cert20_seen_15_35_1 cert20_layer_15_35_1 25 cert20_layer_15_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.b LColor.p 25 cert20_seen_15_35_2 = cert20_component_15_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 15 []) LColor.b LColor.p
    cert20_seen_15_35_2 cert20_layer_15_35_2 24 cert20_layer_15_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 15 [])
      LColor.b LColor.p 24 cert20_seen_15_35_3 = cert20_component_15_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 15 []) LColor.b LColor.p
    cert20_seen_15_35_3 cert20_layer_15_35_3_eq 24

theorem cert20_step_15_35 :
    closedCollarIndexStepBool word fiber20 15 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_15_35)
    (by decide) (by decide)
    (by simpa [cert20_move_15_35] using cert20_component_15_35_eq)
    (by decide) (by decide) (by decide)

def cert20_move_16_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_16_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_0 = cert20_layer_16_4_0 := by
  decide

def cert20_seen_16_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_16_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_16_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_1 = cert20_layer_16_4_1 := by
  decide

def cert20_seen_16_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_16_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_16_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_2 = cert20_layer_16_4_2 := by
  decide

def cert20_seen_16_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_16_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_16_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_3 = cert20_layer_16_4_3 := by
  decide

def cert20_seen_16_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_16_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_16_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_4 = cert20_layer_16_4_4 := by
  decide

def cert20_seen_16_4_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_16_4_5 : List ChainEdge :=
  []

theorem cert20_layer_16_4_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.r LColor.b cert20_seen_16_4_5 = cert20_layer_16_4_5 := by
  decide

theorem cert20_component_16_4_eq :
    closedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_16_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 27 cert20_seen_16_4_0 = cert20_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_0 cert20_layer_16_4_0 26 cert20_layer_16_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 26 cert20_seen_16_4_1 = cert20_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_1 cert20_layer_16_4_1 25 cert20_layer_16_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 25 cert20_seen_16_4_2 = cert20_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_2 cert20_layer_16_4_2 24 cert20_layer_16_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 24 cert20_seen_16_4_3 = cert20_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_3 cert20_layer_16_4_3 23 cert20_layer_16_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 23 cert20_seen_16_4_4 = cert20_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_4 cert20_layer_16_4_4 22 cert20_layer_16_4_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.r LColor.b 22 cert20_seen_16_4_5 = cert20_component_16_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 16 []) LColor.r LColor.b
    cert20_seen_16_4_5 cert20_layer_16_4_5_eq 22

theorem cert20_step_16_4 :
    closedCollarIndexStepBool word fiber20 16 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_16_4)
    (by decide) (by decide)
    (by simpa [cert20_move_16_4] using cert20_component_16_4_eq)
    (by decide) (by decide) (by decide)

def cert20_move_16_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_16_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_16_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_16_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_16_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.b LColor.p cert20_seen_16_36_0 = cert20_layer_16_36_0 := by
  decide

def cert20_seen_16_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_16_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_16_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.b LColor.p cert20_seen_16_36_1 = cert20_layer_16_36_1 := by
  decide

def cert20_seen_16_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_16_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_16_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.b LColor.p cert20_seen_16_36_2 = cert20_layer_16_36_2 := by
  decide

def cert20_seen_16_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_16_36_3 : List ChainEdge :=
  []

theorem cert20_layer_16_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 16 [])
      LColor.b LColor.p cert20_seen_16_36_3 = cert20_layer_16_36_3 := by
  decide

theorem cert20_component_16_36_eq :
    closedCollarComponent word (listGetD fiber20 16 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_16_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 16 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.b LColor.p 27 cert20_seen_16_36_0 = cert20_component_16_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.b LColor.p
    cert20_seen_16_36_0 cert20_layer_16_36_0 26 cert20_layer_16_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.b LColor.p 26 cert20_seen_16_36_1 = cert20_component_16_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.b LColor.p
    cert20_seen_16_36_1 cert20_layer_16_36_1 25 cert20_layer_16_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.b LColor.p 25 cert20_seen_16_36_2 = cert20_component_16_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 16 []) LColor.b LColor.p
    cert20_seen_16_36_2 cert20_layer_16_36_2 24 cert20_layer_16_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 16 [])
      LColor.b LColor.p 24 cert20_seen_16_36_3 = cert20_component_16_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 16 []) LColor.b LColor.p
    cert20_seen_16_36_3 cert20_layer_16_36_3_eq 24

theorem cert20_step_16_36 :
    closedCollarIndexStepBool word fiber20 16 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_16_36)
    (by decide) (by decide)
    (by simpa [cert20_move_16_36] using cert20_component_16_36_eq)
    (by decide) (by decide) (by decide)

def cert20_move_17_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_17_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_0 = cert20_layer_17_5_0 := by
  decide

def cert20_seen_17_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_17_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_17_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_1 = cert20_layer_17_5_1 := by
  decide

def cert20_seen_17_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_17_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_17_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_2 = cert20_layer_17_5_2 := by
  decide

def cert20_seen_17_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_17_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_17_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_3 = cert20_layer_17_5_3 := by
  decide

def cert20_seen_17_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_17_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_17_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_4 = cert20_layer_17_5_4 := by
  decide

def cert20_seen_17_5_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_17_5_5 : List ChainEdge :=
  []

theorem cert20_layer_17_5_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.r LColor.b cert20_seen_17_5_5 = cert20_layer_17_5_5 := by
  decide

theorem cert20_component_17_5_eq :
    closedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_17_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 27 cert20_seen_17_5_0 = cert20_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_0 cert20_layer_17_5_0 26 cert20_layer_17_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 26 cert20_seen_17_5_1 = cert20_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_1 cert20_layer_17_5_1 25 cert20_layer_17_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 25 cert20_seen_17_5_2 = cert20_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_2 cert20_layer_17_5_2 24 cert20_layer_17_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 24 cert20_seen_17_5_3 = cert20_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_3 cert20_layer_17_5_3 23 cert20_layer_17_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 23 cert20_seen_17_5_4 = cert20_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_4 cert20_layer_17_5_4 22 cert20_layer_17_5_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.r LColor.b 22 cert20_seen_17_5_5 = cert20_component_17_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 17 []) LColor.r LColor.b
    cert20_seen_17_5_5 cert20_layer_17_5_5_eq 22

theorem cert20_step_17_5 :
    closedCollarIndexStepBool word fiber20 17 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_17_5)
    (by decide) (by decide)
    (by simpa [cert20_move_17_5] using cert20_component_17_5_eq)
    (by decide) (by decide) (by decide)

def cert20_move_17_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_17_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_17_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_17_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_17_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.b LColor.p cert20_seen_17_37_0 = cert20_layer_17_37_0 := by
  decide

def cert20_seen_17_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_17_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_17_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.b LColor.p cert20_seen_17_37_1 = cert20_layer_17_37_1 := by
  decide

def cert20_seen_17_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_17_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_17_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.b LColor.p cert20_seen_17_37_2 = cert20_layer_17_37_2 := by
  decide

def cert20_seen_17_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_17_37_3 : List ChainEdge :=
  []

theorem cert20_layer_17_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 17 [])
      LColor.b LColor.p cert20_seen_17_37_3 = cert20_layer_17_37_3 := by
  decide

theorem cert20_component_17_37_eq :
    closedCollarComponent word (listGetD fiber20 17 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_17_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 17 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.b LColor.p 27 cert20_seen_17_37_0 = cert20_component_17_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.b LColor.p
    cert20_seen_17_37_0 cert20_layer_17_37_0 26 cert20_layer_17_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.b LColor.p 26 cert20_seen_17_37_1 = cert20_component_17_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.b LColor.p
    cert20_seen_17_37_1 cert20_layer_17_37_1 25 cert20_layer_17_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.b LColor.p 25 cert20_seen_17_37_2 = cert20_component_17_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 17 []) LColor.b LColor.p
    cert20_seen_17_37_2 cert20_layer_17_37_2 24 cert20_layer_17_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 17 [])
      LColor.b LColor.p 24 cert20_seen_17_37_3 = cert20_component_17_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 17 []) LColor.b LColor.p
    cert20_seen_17_37_3 cert20_layer_17_37_3_eq 24

theorem cert20_step_17_37 :
    closedCollarIndexStepBool word fiber20 17 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_17_37)
    (by decide) (by decide)
    (by simpa [cert20_move_17_37] using cert20_component_17_37_eq)
    (by decide) (by decide) (by decide)

def cert20_move_18_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_18_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_18_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 18 [])
      LColor.r LColor.b cert20_seen_18_6_0 = cert20_layer_18_6_0 := by
  decide

def cert20_seen_18_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_18_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_18_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 18 [])
      LColor.r LColor.b cert20_seen_18_6_1 = cert20_layer_18_6_1 := by
  decide

def cert20_seen_18_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_18_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_18_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 18 [])
      LColor.r LColor.b cert20_seen_18_6_2 = cert20_layer_18_6_2 := by
  decide

def cert20_seen_18_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_18_6_3 : List ChainEdge :=
  []

theorem cert20_layer_18_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 18 [])
      LColor.r LColor.b cert20_seen_18_6_3 = cert20_layer_18_6_3 := by
  decide

theorem cert20_component_18_6_eq :
    closedCollarComponent word (listGetD fiber20 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_18_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 18 [])
      LColor.r LColor.b 27 cert20_seen_18_6_0 = cert20_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 18 []) LColor.r LColor.b
    cert20_seen_18_6_0 cert20_layer_18_6_0 26 cert20_layer_18_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 18 [])
      LColor.r LColor.b 26 cert20_seen_18_6_1 = cert20_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 18 []) LColor.r LColor.b
    cert20_seen_18_6_1 cert20_layer_18_6_1 25 cert20_layer_18_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 18 [])
      LColor.r LColor.b 25 cert20_seen_18_6_2 = cert20_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 18 []) LColor.r LColor.b
    cert20_seen_18_6_2 cert20_layer_18_6_2 24 cert20_layer_18_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 18 [])
      LColor.r LColor.b 24 cert20_seen_18_6_3 = cert20_component_18_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 18 []) LColor.r LColor.b
    cert20_seen_18_6_3 cert20_layer_18_6_3_eq 24

theorem cert20_step_18_6 :
    closedCollarIndexStepBool word fiber20 18 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_18_6)
    (by decide) (by decide)
    (by simpa [cert20_move_18_6] using cert20_component_18_6_eq)
    (by decide) (by decide) (by decide)

def cert20_move_19_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_19_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_19_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 19 [])
      LColor.r LColor.b cert20_seen_19_7_0 = cert20_layer_19_7_0 := by
  decide

def cert20_seen_19_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_19_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_19_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 19 [])
      LColor.r LColor.b cert20_seen_19_7_1 = cert20_layer_19_7_1 := by
  decide

def cert20_seen_19_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_19_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_19_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 19 [])
      LColor.r LColor.b cert20_seen_19_7_2 = cert20_layer_19_7_2 := by
  decide

def cert20_seen_19_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_19_7_3 : List ChainEdge :=
  []

theorem cert20_layer_19_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 19 [])
      LColor.r LColor.b cert20_seen_19_7_3 = cert20_layer_19_7_3 := by
  decide

theorem cert20_component_19_7_eq :
    closedCollarComponent word (listGetD fiber20 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_19_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 19 [])
      LColor.r LColor.b 27 cert20_seen_19_7_0 = cert20_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 19 []) LColor.r LColor.b
    cert20_seen_19_7_0 cert20_layer_19_7_0 26 cert20_layer_19_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 19 [])
      LColor.r LColor.b 26 cert20_seen_19_7_1 = cert20_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 19 []) LColor.r LColor.b
    cert20_seen_19_7_1 cert20_layer_19_7_1 25 cert20_layer_19_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 19 [])
      LColor.r LColor.b 25 cert20_seen_19_7_2 = cert20_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 19 []) LColor.r LColor.b
    cert20_seen_19_7_2 cert20_layer_19_7_2 24 cert20_layer_19_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 19 [])
      LColor.r LColor.b 24 cert20_seen_19_7_3 = cert20_component_19_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 19 []) LColor.r LColor.b
    cert20_seen_19_7_3 cert20_layer_19_7_3_eq 24

theorem cert20_step_19_7 :
    closedCollarIndexStepBool word fiber20 19 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_19_7)
    (by decide) (by decide)
    (by simpa [cert20_move_19_7] using cert20_component_19_7_eq)
    (by decide) (by decide) (by decide)

def cert20_move_20_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_20_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_20_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.r LColor.b cert20_seen_20_8_0 = cert20_layer_20_8_0 := by
  decide

def cert20_seen_20_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_20_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_20_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.r LColor.b cert20_seen_20_8_1 = cert20_layer_20_8_1 := by
  decide

def cert20_seen_20_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_20_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_20_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.r LColor.b cert20_seen_20_8_2 = cert20_layer_20_8_2 := by
  decide

def cert20_seen_20_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_20_8_3 : List ChainEdge :=
  []

theorem cert20_layer_20_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.r LColor.b cert20_seen_20_8_3 = cert20_layer_20_8_3 := by
  decide

theorem cert20_component_20_8_eq :
    closedCollarComponent word (listGetD fiber20 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_20_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.r LColor.b 27 cert20_seen_20_8_0 = cert20_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.r LColor.b
    cert20_seen_20_8_0 cert20_layer_20_8_0 26 cert20_layer_20_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.r LColor.b 26 cert20_seen_20_8_1 = cert20_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.r LColor.b
    cert20_seen_20_8_1 cert20_layer_20_8_1 25 cert20_layer_20_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.r LColor.b 25 cert20_seen_20_8_2 = cert20_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.r LColor.b
    cert20_seen_20_8_2 cert20_layer_20_8_2 24 cert20_layer_20_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.r LColor.b 24 cert20_seen_20_8_3 = cert20_component_20_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 20 []) LColor.r LColor.b
    cert20_seen_20_8_3 cert20_layer_20_8_3_eq 24

theorem cert20_step_20_8 :
    closedCollarIndexStepBool word fiber20 20 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_20_8)
    (by decide) (by decide)
    (by simpa [cert20_move_20_8] using cert20_component_20_8_eq)
    (by decide) (by decide) (by decide)

def cert20_move_20_40 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_20_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_20_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_20_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_20_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.b LColor.p cert20_seen_20_40_0 = cert20_layer_20_40_0 := by
  decide

def cert20_seen_20_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_20_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_20_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.b LColor.p cert20_seen_20_40_1 = cert20_layer_20_40_1 := by
  decide

def cert20_seen_20_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_20_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_20_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.b LColor.p cert20_seen_20_40_2 = cert20_layer_20_40_2 := by
  decide

def cert20_seen_20_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_20_40_3 : List ChainEdge :=
  []

theorem cert20_layer_20_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 20 [])
      LColor.b LColor.p cert20_seen_20_40_3 = cert20_layer_20_40_3 := by
  decide

theorem cert20_component_20_40_eq :
    closedCollarComponent word (listGetD fiber20 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_20_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 20 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.b LColor.p 27 cert20_seen_20_40_0 = cert20_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.b LColor.p
    cert20_seen_20_40_0 cert20_layer_20_40_0 26 cert20_layer_20_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.b LColor.p 26 cert20_seen_20_40_1 = cert20_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.b LColor.p
    cert20_seen_20_40_1 cert20_layer_20_40_1 25 cert20_layer_20_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.b LColor.p 25 cert20_seen_20_40_2 = cert20_component_20_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 20 []) LColor.b LColor.p
    cert20_seen_20_40_2 cert20_layer_20_40_2 24 cert20_layer_20_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 20 [])
      LColor.b LColor.p 24 cert20_seen_20_40_3 = cert20_component_20_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 20 []) LColor.b LColor.p
    cert20_seen_20_40_3 cert20_layer_20_40_3_eq 24

theorem cert20_step_20_40 :
    closedCollarIndexStepBool word fiber20 20 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_20_40)
    (by decide) (by decide)
    (by simpa [cert20_move_20_40] using cert20_component_20_40_eq)
    (by decide) (by decide) (by decide)

def cert20_move_21_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_21_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_21_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.r LColor.b cert20_seen_21_9_0 = cert20_layer_21_9_0 := by
  decide

def cert20_seen_21_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_21_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_21_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.r LColor.b cert20_seen_21_9_1 = cert20_layer_21_9_1 := by
  decide

def cert20_seen_21_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_21_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_21_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.r LColor.b cert20_seen_21_9_2 = cert20_layer_21_9_2 := by
  decide

def cert20_seen_21_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_21_9_3 : List ChainEdge :=
  []

theorem cert20_layer_21_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.r LColor.b cert20_seen_21_9_3 = cert20_layer_21_9_3 := by
  decide

theorem cert20_component_21_9_eq :
    closedCollarComponent word (listGetD fiber20 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_21_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.r LColor.b 27 cert20_seen_21_9_0 = cert20_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.r LColor.b
    cert20_seen_21_9_0 cert20_layer_21_9_0 26 cert20_layer_21_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.r LColor.b 26 cert20_seen_21_9_1 = cert20_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.r LColor.b
    cert20_seen_21_9_1 cert20_layer_21_9_1 25 cert20_layer_21_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.r LColor.b 25 cert20_seen_21_9_2 = cert20_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.r LColor.b
    cert20_seen_21_9_2 cert20_layer_21_9_2 24 cert20_layer_21_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.r LColor.b 24 cert20_seen_21_9_3 = cert20_component_21_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 21 []) LColor.r LColor.b
    cert20_seen_21_9_3 cert20_layer_21_9_3_eq 24

theorem cert20_step_21_9 :
    closedCollarIndexStepBool word fiber20 21 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_21_9)
    (by decide) (by decide)
    (by simpa [cert20_move_21_9] using cert20_component_21_9_eq)
    (by decide) (by decide) (by decide)

def cert20_move_21_41 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_21_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_21_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_21_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_21_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.b LColor.p cert20_seen_21_41_0 = cert20_layer_21_41_0 := by
  decide

def cert20_seen_21_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_21_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_21_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.b LColor.p cert20_seen_21_41_1 = cert20_layer_21_41_1 := by
  decide

def cert20_seen_21_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_21_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_21_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.b LColor.p cert20_seen_21_41_2 = cert20_layer_21_41_2 := by
  decide

def cert20_seen_21_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_21_41_3 : List ChainEdge :=
  []

theorem cert20_layer_21_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 21 [])
      LColor.b LColor.p cert20_seen_21_41_3 = cert20_layer_21_41_3 := by
  decide

theorem cert20_component_21_41_eq :
    closedCollarComponent word (listGetD fiber20 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_21_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 21 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.b LColor.p 27 cert20_seen_21_41_0 = cert20_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.b LColor.p
    cert20_seen_21_41_0 cert20_layer_21_41_0 26 cert20_layer_21_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.b LColor.p 26 cert20_seen_21_41_1 = cert20_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.b LColor.p
    cert20_seen_21_41_1 cert20_layer_21_41_1 25 cert20_layer_21_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.b LColor.p 25 cert20_seen_21_41_2 = cert20_component_21_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 21 []) LColor.b LColor.p
    cert20_seen_21_41_2 cert20_layer_21_41_2 24 cert20_layer_21_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 21 [])
      LColor.b LColor.p 24 cert20_seen_21_41_3 = cert20_component_21_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 21 []) LColor.b LColor.p
    cert20_seen_21_41_3 cert20_layer_21_41_3_eq 24

theorem cert20_step_21_41 :
    closedCollarIndexStepBool word fiber20 21 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_21_41)
    (by decide) (by decide)
    (by simpa [cert20_move_21_41] using cert20_component_21_41_eq)
    (by decide) (by decide) (by decide)

def cert20_move_22_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_22_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_22_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_0 = cert20_layer_22_10_0 := by
  decide

def cert20_seen_22_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_22_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_22_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_1 = cert20_layer_22_10_1 := by
  decide

def cert20_seen_22_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_22_10_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_22_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_2 = cert20_layer_22_10_2 := by
  decide

def cert20_seen_22_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_22_10_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_22_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_3 = cert20_layer_22_10_3 := by
  decide

def cert20_seen_22_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_22_10_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_22_10_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_4 = cert20_layer_22_10_4 := by
  decide

def cert20_seen_22_10_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_22_10_5 : List ChainEdge :=
  []

theorem cert20_layer_22_10_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 22 [])
      LColor.r LColor.b cert20_seen_22_10_5 = cert20_layer_22_10_5 := by
  decide

theorem cert20_component_22_10_eq :
    closedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_22_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 27 cert20_seen_22_10_0 = cert20_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_0 cert20_layer_22_10_0 26 cert20_layer_22_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 26 cert20_seen_22_10_1 = cert20_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_1 cert20_layer_22_10_1 25 cert20_layer_22_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 25 cert20_seen_22_10_2 = cert20_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_2 cert20_layer_22_10_2 24 cert20_layer_22_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 24 cert20_seen_22_10_3 = cert20_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_3 cert20_layer_22_10_3 23 cert20_layer_22_10_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 23 cert20_seen_22_10_4 = cert20_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_4 cert20_layer_22_10_4 22 cert20_layer_22_10_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 22 [])
      LColor.r LColor.b 22 cert20_seen_22_10_5 = cert20_component_22_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 22 []) LColor.r LColor.b
    cert20_seen_22_10_5 cert20_layer_22_10_5_eq 22

theorem cert20_step_22_10 :
    closedCollarIndexStepBool word fiber20 22 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_22_10)
    (by decide) (by decide)
    (by simpa [cert20_move_22_10] using cert20_component_22_10_eq)
    (by decide) (by decide) (by decide)

def cert20_move_23_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_23_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_seen_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_23_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_0 = cert20_layer_23_11_0 := by
  decide

def cert20_seen_23_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_23_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_23_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_1 = cert20_layer_23_11_1 := by
  decide

def cert20_seen_23_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_23_11_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert20_layer_23_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_2 = cert20_layer_23_11_2 := by
  decide

def cert20_seen_23_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert20_layer_23_11_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert20_layer_23_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_3 = cert20_layer_23_11_3 := by
  decide

def cert20_seen_23_11_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert20_layer_23_11_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert20_layer_23_11_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_4 = cert20_layer_23_11_4 := by
  decide

def cert20_seen_23_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert20_layer_23_11_5 : List ChainEdge :=
  []

theorem cert20_layer_23_11_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 23 [])
      LColor.r LColor.b cert20_seen_23_11_5 = cert20_layer_23_11_5 := by
  decide

theorem cert20_component_23_11_eq :
    closedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert20_component_23_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 27 cert20_seen_23_11_0 = cert20_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_0 cert20_layer_23_11_0 26 cert20_layer_23_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 26 cert20_seen_23_11_1 = cert20_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_1 cert20_layer_23_11_1 25 cert20_layer_23_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 25 cert20_seen_23_11_2 = cert20_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_2 cert20_layer_23_11_2 24 cert20_layer_23_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 24 cert20_seen_23_11_3 = cert20_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_3 cert20_layer_23_11_3 23 cert20_layer_23_11_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 23 cert20_seen_23_11_4 = cert20_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_4 cert20_layer_23_11_4 22 cert20_layer_23_11_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 23 [])
      LColor.r LColor.b 22 cert20_seen_23_11_5 = cert20_component_23_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 23 []) LColor.r LColor.b
    cert20_seen_23_11_5 cert20_layer_23_11_5_eq 22

theorem cert20_step_23_11 :
    closedCollarIndexStepBool word fiber20 23 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_23_11)
    (by decide) (by decide)
    (by simpa [cert20_move_23_11] using cert20_component_23_11_eq)
    (by decide) (by decide) (by decide)

def cert20_move_24_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_24_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_24_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_24_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_0 = cert20_layer_24_2_0 := by
  decide

def cert20_seen_24_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_24_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_24_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_1 = cert20_layer_24_2_1 := by
  decide

def cert20_seen_24_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_24_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_24_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_2 = cert20_layer_24_2_2 := by
  decide

def cert20_seen_24_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_24_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_24_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_3 = cert20_layer_24_2_3 := by
  decide

def cert20_seen_24_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_24_2_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_24_2_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_4 = cert20_layer_24_2_4 := by
  decide

def cert20_seen_24_2_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_24_2_5 : List ChainEdge :=
  []

theorem cert20_layer_24_2_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.b LColor.p cert20_seen_24_2_5 = cert20_layer_24_2_5 := by
  decide

theorem cert20_component_24_2_eq :
    closedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_24_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 24 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 27 cert20_seen_24_2_0 = cert20_component_24_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_0 cert20_layer_24_2_0 26 cert20_layer_24_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 26 cert20_seen_24_2_1 = cert20_component_24_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_1 cert20_layer_24_2_1 25 cert20_layer_24_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 25 cert20_seen_24_2_2 = cert20_component_24_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_2 cert20_layer_24_2_2 24 cert20_layer_24_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 24 cert20_seen_24_2_3 = cert20_component_24_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_3 cert20_layer_24_2_3 23 cert20_layer_24_2_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 23 cert20_seen_24_2_4 = cert20_component_24_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_4 cert20_layer_24_2_4 22 cert20_layer_24_2_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.b LColor.p 22 cert20_seen_24_2_5 = cert20_component_24_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 24 []) LColor.b LColor.p
    cert20_seen_24_2_5 cert20_layer_24_2_5_eq 22

theorem cert20_step_24_2 :
    closedCollarIndexStepBool word fiber20 24 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_24_2)
    (by decide) (by decide)
    (by simpa [cert20_move_24_2] using cert20_component_24_2_eq)
    (by decide) (by decide) (by decide)

def cert20_move_24_42 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_24_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_24_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_24_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_24_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.r LColor.p cert20_seen_24_42_0 = cert20_layer_24_42_0 := by
  decide

def cert20_seen_24_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_24_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_24_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.r LColor.p cert20_seen_24_42_1 = cert20_layer_24_42_1 := by
  decide

def cert20_seen_24_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_24_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_24_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.r LColor.p cert20_seen_24_42_2 = cert20_layer_24_42_2 := by
  decide

def cert20_seen_24_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_24_42_3 : List ChainEdge :=
  []

theorem cert20_layer_24_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 24 [])
      LColor.r LColor.p cert20_seen_24_42_3 = cert20_layer_24_42_3 := by
  decide

theorem cert20_component_24_42_eq :
    closedCollarComponent word (listGetD fiber20 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_24_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.r LColor.p 27 cert20_seen_24_42_0 = cert20_component_24_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.r LColor.p
    cert20_seen_24_42_0 cert20_layer_24_42_0 26 cert20_layer_24_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.r LColor.p 26 cert20_seen_24_42_1 = cert20_component_24_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.r LColor.p
    cert20_seen_24_42_1 cert20_layer_24_42_1 25 cert20_layer_24_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.r LColor.p 25 cert20_seen_24_42_2 = cert20_component_24_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 24 []) LColor.r LColor.p
    cert20_seen_24_42_2 cert20_layer_24_42_2 24 cert20_layer_24_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 24 [])
      LColor.r LColor.p 24 cert20_seen_24_42_3 = cert20_component_24_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 24 []) LColor.r LColor.p
    cert20_seen_24_42_3 cert20_layer_24_42_3_eq 24

theorem cert20_step_24_42 :
    closedCollarIndexStepBool word fiber20 24 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_24_42)
    (by decide) (by decide)
    (by simpa [cert20_move_24_42] using cert20_component_24_42_eq)
    (by decide) (by decide) (by decide)

def cert20_move_25_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_25_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_25_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_25_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_0 = cert20_layer_25_3_0 := by
  decide

def cert20_seen_25_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_25_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_25_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_1 = cert20_layer_25_3_1 := by
  decide

def cert20_seen_25_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_25_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_25_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_2 = cert20_layer_25_3_2 := by
  decide

def cert20_seen_25_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_25_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_25_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_3 = cert20_layer_25_3_3 := by
  decide

def cert20_seen_25_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_25_3_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_25_3_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_4 = cert20_layer_25_3_4 := by
  decide

def cert20_seen_25_3_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_25_3_5 : List ChainEdge :=
  []

theorem cert20_layer_25_3_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.b LColor.p cert20_seen_25_3_5 = cert20_layer_25_3_5 := by
  decide

theorem cert20_component_25_3_eq :
    closedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_25_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 25 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 27 cert20_seen_25_3_0 = cert20_component_25_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_0 cert20_layer_25_3_0 26 cert20_layer_25_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 26 cert20_seen_25_3_1 = cert20_component_25_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_1 cert20_layer_25_3_1 25 cert20_layer_25_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 25 cert20_seen_25_3_2 = cert20_component_25_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_2 cert20_layer_25_3_2 24 cert20_layer_25_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 24 cert20_seen_25_3_3 = cert20_component_25_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_3 cert20_layer_25_3_3 23 cert20_layer_25_3_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 23 cert20_seen_25_3_4 = cert20_component_25_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_4 cert20_layer_25_3_4 22 cert20_layer_25_3_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.b LColor.p 22 cert20_seen_25_3_5 = cert20_component_25_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 25 []) LColor.b LColor.p
    cert20_seen_25_3_5 cert20_layer_25_3_5_eq 22

theorem cert20_step_25_3 :
    closedCollarIndexStepBool word fiber20 25 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_25_3)
    (by decide) (by decide)
    (by simpa [cert20_move_25_3] using cert20_component_25_3_eq)
    (by decide) (by decide) (by decide)

def cert20_move_25_43 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_25_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_25_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_25_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_25_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.r LColor.p cert20_seen_25_43_0 = cert20_layer_25_43_0 := by
  decide

def cert20_seen_25_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_25_43_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_25_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.r LColor.p cert20_seen_25_43_1 = cert20_layer_25_43_1 := by
  decide

def cert20_seen_25_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_25_43_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_25_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.r LColor.p cert20_seen_25_43_2 = cert20_layer_25_43_2 := by
  decide

def cert20_seen_25_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_25_43_3 : List ChainEdge :=
  []

theorem cert20_layer_25_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 25 [])
      LColor.r LColor.p cert20_seen_25_43_3 = cert20_layer_25_43_3 := by
  decide

theorem cert20_component_25_43_eq :
    closedCollarComponent word (listGetD fiber20 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_25_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.r LColor.p 27 cert20_seen_25_43_0 = cert20_component_25_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.r LColor.p
    cert20_seen_25_43_0 cert20_layer_25_43_0 26 cert20_layer_25_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.r LColor.p 26 cert20_seen_25_43_1 = cert20_component_25_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.r LColor.p
    cert20_seen_25_43_1 cert20_layer_25_43_1 25 cert20_layer_25_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.r LColor.p 25 cert20_seen_25_43_2 = cert20_component_25_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 25 []) LColor.r LColor.p
    cert20_seen_25_43_2 cert20_layer_25_43_2 24 cert20_layer_25_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 25 [])
      LColor.r LColor.p 24 cert20_seen_25_43_3 = cert20_component_25_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 25 []) LColor.r LColor.p
    cert20_seen_25_43_3 cert20_layer_25_43_3_eq 24

theorem cert20_step_25_43 :
    closedCollarIndexStepBool word fiber20 25 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_25_43)
    (by decide) (by decide)
    (by simpa [cert20_move_25_43] using cert20_component_25_43_eq)
    (by decide) (by decide) (by decide)

def cert20_move_26_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_26_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_26_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_26_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.b LColor.p cert20_seen_26_4_0 = cert20_layer_26_4_0 := by
  decide

def cert20_seen_26_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_26_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_26_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.b LColor.p cert20_seen_26_4_1 = cert20_layer_26_4_1 := by
  decide

def cert20_seen_26_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_26_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_26_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.b LColor.p cert20_seen_26_4_2 = cert20_layer_26_4_2 := by
  decide

def cert20_seen_26_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_26_4_3 : List ChainEdge :=
  []

theorem cert20_layer_26_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.b LColor.p cert20_seen_26_4_3 = cert20_layer_26_4_3 := by
  decide

theorem cert20_component_26_4_eq :
    closedCollarComponent word (listGetD fiber20 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_26_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.b LColor.p 27 cert20_seen_26_4_0 = cert20_component_26_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.b LColor.p
    cert20_seen_26_4_0 cert20_layer_26_4_0 26 cert20_layer_26_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.b LColor.p 26 cert20_seen_26_4_1 = cert20_component_26_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.b LColor.p
    cert20_seen_26_4_1 cert20_layer_26_4_1 25 cert20_layer_26_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.b LColor.p 25 cert20_seen_26_4_2 = cert20_component_26_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.b LColor.p
    cert20_seen_26_4_2 cert20_layer_26_4_2 24 cert20_layer_26_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.b LColor.p 24 cert20_seen_26_4_3 = cert20_component_26_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 26 []) LColor.b LColor.p
    cert20_seen_26_4_3 cert20_layer_26_4_3_eq 24

theorem cert20_step_26_4 :
    closedCollarIndexStepBool word fiber20 26 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_26_4)
    (by decide) (by decide)
    (by simpa [cert20_move_26_4] using cert20_component_26_4_eq)
    (by decide) (by decide) (by decide)

def cert20_move_26_39 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_26_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_seen_26_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_26_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_26_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_0 = cert20_layer_26_39_0 := by
  decide

def cert20_seen_26_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_26_39_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_26_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_1 = cert20_layer_26_39_1 := by
  decide

def cert20_seen_26_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_26_39_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_26_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_2 = cert20_layer_26_39_2 := by
  decide

def cert20_seen_26_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_26_39_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_26_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_3 = cert20_layer_26_39_3 := by
  decide

def cert20_seen_26_39_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_26_39_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert20_layer_26_39_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_4 = cert20_layer_26_39_4 := by
  decide

def cert20_seen_26_39_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_26_39_5 : List ChainEdge :=
  []

theorem cert20_layer_26_39_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 26 [])
      LColor.r LColor.p cert20_seen_26_39_5 = cert20_layer_26_39_5 := by
  decide

theorem cert20_component_26_39_eq :
    closedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_26_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 27 cert20_seen_26_39_0 = cert20_component_26_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_0 cert20_layer_26_39_0 26 cert20_layer_26_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 26 cert20_seen_26_39_1 = cert20_component_26_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_1 cert20_layer_26_39_1 25 cert20_layer_26_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 25 cert20_seen_26_39_2 = cert20_component_26_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_2 cert20_layer_26_39_2 24 cert20_layer_26_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 24 cert20_seen_26_39_3 = cert20_component_26_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_3 cert20_layer_26_39_3 23 cert20_layer_26_39_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 23 cert20_seen_26_39_4 = cert20_component_26_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_4 cert20_layer_26_39_4 22 cert20_layer_26_39_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 26 [])
      LColor.r LColor.p 22 cert20_seen_26_39_5 = cert20_component_26_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 26 []) LColor.r LColor.p
    cert20_seen_26_39_5 cert20_layer_26_39_5_eq 22

theorem cert20_step_26_39 :
    closedCollarIndexStepBool word fiber20 26 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_26_39)
    (by decide) (by decide)
    (by simpa [cert20_move_26_39] using cert20_component_26_39_eq)
    (by decide) (by decide) (by decide)

def cert20_move_27_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_27_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_27_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_27_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_27_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.b LColor.p cert20_seen_27_5_0 = cert20_layer_27_5_0 := by
  decide

def cert20_seen_27_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_27_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_27_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.b LColor.p cert20_seen_27_5_1 = cert20_layer_27_5_1 := by
  decide

def cert20_seen_27_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_27_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_27_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.b LColor.p cert20_seen_27_5_2 = cert20_layer_27_5_2 := by
  decide

def cert20_seen_27_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_27_5_3 : List ChainEdge :=
  []

theorem cert20_layer_27_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.b LColor.p cert20_seen_27_5_3 = cert20_layer_27_5_3 := by
  decide

theorem cert20_component_27_5_eq :
    closedCollarComponent word (listGetD fiber20 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_27_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.b LColor.p 27 cert20_seen_27_5_0 = cert20_component_27_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.b LColor.p
    cert20_seen_27_5_0 cert20_layer_27_5_0 26 cert20_layer_27_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.b LColor.p 26 cert20_seen_27_5_1 = cert20_component_27_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.b LColor.p
    cert20_seen_27_5_1 cert20_layer_27_5_1 25 cert20_layer_27_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.b LColor.p 25 cert20_seen_27_5_2 = cert20_component_27_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.b LColor.p
    cert20_seen_27_5_2 cert20_layer_27_5_2 24 cert20_layer_27_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.b LColor.p 24 cert20_seen_27_5_3 = cert20_component_27_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 27 []) LColor.b LColor.p
    cert20_seen_27_5_3 cert20_layer_27_5_3_eq 24

theorem cert20_step_27_5 :
    closedCollarIndexStepBool word fiber20 27 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_27_5)
    (by decide) (by decide)
    (by simpa [cert20_move_27_5] using cert20_component_27_5_eq)
    (by decide) (by decide) (by decide)

def cert20_move_27_38 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_27_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_seen_27_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_27_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_27_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_0 = cert20_layer_27_38_0 := by
  decide

def cert20_seen_27_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_27_38_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_27_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_1 = cert20_layer_27_38_1 := by
  decide

def cert20_seen_27_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_27_38_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_27_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_2 = cert20_layer_27_38_2 := by
  decide

def cert20_seen_27_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_27_38_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_27_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_3 = cert20_layer_27_38_3 := by
  decide

def cert20_seen_27_38_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_27_38_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert20_layer_27_38_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_4 = cert20_layer_27_38_4 := by
  decide

def cert20_seen_27_38_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_27_38_5 : List ChainEdge :=
  []

theorem cert20_layer_27_38_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 27 [])
      LColor.r LColor.p cert20_seen_27_38_5 = cert20_layer_27_38_5 := by
  decide

theorem cert20_component_27_38_eq :
    closedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_27_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 27 cert20_seen_27_38_0 = cert20_component_27_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_0 cert20_layer_27_38_0 26 cert20_layer_27_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 26 cert20_seen_27_38_1 = cert20_component_27_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_1 cert20_layer_27_38_1 25 cert20_layer_27_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 25 cert20_seen_27_38_2 = cert20_component_27_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_2 cert20_layer_27_38_2 24 cert20_layer_27_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 24 cert20_seen_27_38_3 = cert20_component_27_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_3 cert20_layer_27_38_3 23 cert20_layer_27_38_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 23 cert20_seen_27_38_4 = cert20_component_27_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_4 cert20_layer_27_38_4 22 cert20_layer_27_38_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 27 [])
      LColor.r LColor.p 22 cert20_seen_27_38_5 = cert20_component_27_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 27 []) LColor.r LColor.p
    cert20_seen_27_38_5 cert20_layer_27_38_5_eq 22

theorem cert20_step_27_38 :
    closedCollarIndexStepBool word fiber20 27 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_27_38)
    (by decide) (by decide)
    (by simpa [cert20_move_27_38] using cert20_component_27_38_eq)
    (by decide) (by decide) (by decide)

def cert20_move_28_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_28_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_seen_28_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_28_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_28_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_0 = cert20_layer_28_8_0 := by
  decide

def cert20_seen_28_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_28_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_28_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_1 = cert20_layer_28_8_1 := by
  decide

def cert20_seen_28_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_28_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_28_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_2 = cert20_layer_28_8_2 := by
  decide

def cert20_seen_28_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_28_8_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_28_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_3 = cert20_layer_28_8_3 := by
  decide

def cert20_seen_28_8_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_28_8_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_28_8_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_4 = cert20_layer_28_8_4 := by
  decide

def cert20_seen_28_8_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_28_8_5 : List ChainEdge :=
  []

theorem cert20_layer_28_8_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 28 [])
      LColor.b LColor.p cert20_seen_28_8_5 = cert20_layer_28_8_5 := by
  decide

theorem cert20_component_28_8_eq :
    closedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_28_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 27 cert20_seen_28_8_0 = cert20_component_28_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_0 cert20_layer_28_8_0 26 cert20_layer_28_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 26 cert20_seen_28_8_1 = cert20_component_28_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_1 cert20_layer_28_8_1 25 cert20_layer_28_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 25 cert20_seen_28_8_2 = cert20_component_28_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_2 cert20_layer_28_8_2 24 cert20_layer_28_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 24 cert20_seen_28_8_3 = cert20_component_28_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_3 cert20_layer_28_8_3 23 cert20_layer_28_8_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 23 cert20_seen_28_8_4 = cert20_component_28_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_4 cert20_layer_28_8_4 22 cert20_layer_28_8_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 28 [])
      LColor.b LColor.p 22 cert20_seen_28_8_5 = cert20_component_28_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 28 []) LColor.b LColor.p
    cert20_seen_28_8_5 cert20_layer_28_8_5_eq 22

theorem cert20_step_28_8 :
    closedCollarIndexStepBool word fiber20 28 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_28_8)
    (by decide) (by decide)
    (by simpa [cert20_move_28_8] using cert20_component_28_8_eq)
    (by decide) (by decide) (by decide)

def cert20_move_29_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_29_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_seen_29_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_29_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_29_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_0 = cert20_layer_29_9_0 := by
  decide

def cert20_seen_29_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_29_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_29_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_1 = cert20_layer_29_9_1 := by
  decide

def cert20_seen_29_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_29_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_29_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_2 = cert20_layer_29_9_2 := by
  decide

def cert20_seen_29_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_29_9_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_29_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_3 = cert20_layer_29_9_3 := by
  decide

def cert20_seen_29_9_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_29_9_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_29_9_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_4 = cert20_layer_29_9_4 := by
  decide

def cert20_seen_29_9_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_29_9_5 : List ChainEdge :=
  []

theorem cert20_layer_29_9_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 29 [])
      LColor.b LColor.p cert20_seen_29_9_5 = cert20_layer_29_9_5 := by
  decide

theorem cert20_component_29_9_eq :
    closedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_29_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 27 cert20_seen_29_9_0 = cert20_component_29_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_0 cert20_layer_29_9_0 26 cert20_layer_29_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 26 cert20_seen_29_9_1 = cert20_component_29_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_1 cert20_layer_29_9_1 25 cert20_layer_29_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 25 cert20_seen_29_9_2 = cert20_component_29_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_2 cert20_layer_29_9_2 24 cert20_layer_29_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 24 cert20_seen_29_9_3 = cert20_component_29_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_3 cert20_layer_29_9_3 23 cert20_layer_29_9_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 23 cert20_seen_29_9_4 = cert20_component_29_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_4 cert20_layer_29_9_4 22 cert20_layer_29_9_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 29 [])
      LColor.b LColor.p 22 cert20_seen_29_9_5 = cert20_component_29_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 29 []) LColor.b LColor.p
    cert20_seen_29_9_5 cert20_layer_29_9_5_eq 22

theorem cert20_step_29_9 :
    closedCollarIndexStepBool word fiber20 29 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_29_9)
    (by decide) (by decide)
    (by simpa [cert20_move_29_9] using cert20_component_29_9_eq)
    (by decide) (by decide) (by decide)

def cert20_move_30_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_30_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_30_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_30_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_30_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 30 [])
      LColor.b LColor.p cert20_seen_30_10_0 = cert20_layer_30_10_0 := by
  decide

def cert20_seen_30_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_30_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_30_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 30 [])
      LColor.b LColor.p cert20_seen_30_10_1 = cert20_layer_30_10_1 := by
  decide

def cert20_seen_30_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_30_10_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_30_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 30 [])
      LColor.b LColor.p cert20_seen_30_10_2 = cert20_layer_30_10_2 := by
  decide

def cert20_seen_30_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_30_10_3 : List ChainEdge :=
  []

theorem cert20_layer_30_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 30 [])
      LColor.b LColor.p cert20_seen_30_10_3 = cert20_layer_30_10_3 := by
  decide

theorem cert20_component_30_10_eq :
    closedCollarComponent word (listGetD fiber20 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_30_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 30 [])
      LColor.b LColor.p 27 cert20_seen_30_10_0 = cert20_component_30_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 30 []) LColor.b LColor.p
    cert20_seen_30_10_0 cert20_layer_30_10_0 26 cert20_layer_30_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 30 [])
      LColor.b LColor.p 26 cert20_seen_30_10_1 = cert20_component_30_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 30 []) LColor.b LColor.p
    cert20_seen_30_10_1 cert20_layer_30_10_1 25 cert20_layer_30_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 30 [])
      LColor.b LColor.p 25 cert20_seen_30_10_2 = cert20_component_30_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 30 []) LColor.b LColor.p
    cert20_seen_30_10_2 cert20_layer_30_10_2 24 cert20_layer_30_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 30 [])
      LColor.b LColor.p 24 cert20_seen_30_10_3 = cert20_component_30_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 30 []) LColor.b LColor.p
    cert20_seen_30_10_3 cert20_layer_30_10_3_eq 24

theorem cert20_step_30_10 :
    closedCollarIndexStepBool word fiber20 30 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_30_10)
    (by decide) (by decide)
    (by simpa [cert20_move_30_10] using cert20_component_30_10_eq)
    (by decide) (by decide) (by decide)

def cert20_move_31_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_31_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_seen_31_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_31_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_31_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 31 [])
      LColor.b LColor.p cert20_seen_31_11_0 = cert20_layer_31_11_0 := by
  decide

def cert20_seen_31_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_31_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_31_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 31 [])
      LColor.b LColor.p cert20_seen_31_11_1 = cert20_layer_31_11_1 := by
  decide

def cert20_seen_31_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_31_11_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_31_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 31 [])
      LColor.b LColor.p cert20_seen_31_11_2 = cert20_layer_31_11_2 := by
  decide

def cert20_seen_31_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_31_11_3 : List ChainEdge :=
  []

theorem cert20_layer_31_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 31 [])
      LColor.b LColor.p cert20_seen_31_11_3 = cert20_layer_31_11_3 := by
  decide

theorem cert20_component_31_11_eq :
    closedCollarComponent word (listGetD fiber20 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_31_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 31 [])
      LColor.b LColor.p 27 cert20_seen_31_11_0 = cert20_component_31_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 31 []) LColor.b LColor.p
    cert20_seen_31_11_0 cert20_layer_31_11_0 26 cert20_layer_31_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 31 [])
      LColor.b LColor.p 26 cert20_seen_31_11_1 = cert20_component_31_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 31 []) LColor.b LColor.p
    cert20_seen_31_11_1 cert20_layer_31_11_1 25 cert20_layer_31_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 31 [])
      LColor.b LColor.p 25 cert20_seen_31_11_2 = cert20_component_31_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 31 []) LColor.b LColor.p
    cert20_seen_31_11_2 cert20_layer_31_11_2 24 cert20_layer_31_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 31 [])
      LColor.b LColor.p 24 cert20_seen_31_11_3 = cert20_component_31_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 31 []) LColor.b LColor.p
    cert20_seen_31_11_3 cert20_layer_31_11_3_eq 24

theorem cert20_step_31_11 :
    closedCollarIndexStepBool word fiber20 31 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_31_11)
    (by decide) (by decide)
    (by simpa [cert20_move_31_11] using cert20_component_31_11_eq)
    (by decide) (by decide) (by decide)

def cert20_move_32_12 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_32_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_32_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_32_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_32_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 32 [])
      LColor.b LColor.p cert20_seen_32_12_0 = cert20_layer_32_12_0 := by
  decide

def cert20_seen_32_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_32_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_32_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 32 [])
      LColor.b LColor.p cert20_seen_32_12_1 = cert20_layer_32_12_1 := by
  decide

def cert20_seen_32_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_32_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_32_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 32 [])
      LColor.b LColor.p cert20_seen_32_12_2 = cert20_layer_32_12_2 := by
  decide

def cert20_seen_32_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_32_12_3 : List ChainEdge :=
  []

theorem cert20_layer_32_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 32 [])
      LColor.b LColor.p cert20_seen_32_12_3 = cert20_layer_32_12_3 := by
  decide

theorem cert20_component_32_12_eq :
    closedCollarComponent word (listGetD fiber20 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_32_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 32 [])
      LColor.b LColor.p 27 cert20_seen_32_12_0 = cert20_component_32_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 32 []) LColor.b LColor.p
    cert20_seen_32_12_0 cert20_layer_32_12_0 26 cert20_layer_32_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 32 [])
      LColor.b LColor.p 26 cert20_seen_32_12_1 = cert20_component_32_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 32 []) LColor.b LColor.p
    cert20_seen_32_12_1 cert20_layer_32_12_1 25 cert20_layer_32_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 32 [])
      LColor.b LColor.p 25 cert20_seen_32_12_2 = cert20_component_32_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 32 []) LColor.b LColor.p
    cert20_seen_32_12_2 cert20_layer_32_12_2 24 cert20_layer_32_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 32 [])
      LColor.b LColor.p 24 cert20_seen_32_12_3 = cert20_component_32_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 32 []) LColor.b LColor.p
    cert20_seen_32_12_3 cert20_layer_32_12_3_eq 24

theorem cert20_step_32_12 :
    closedCollarIndexStepBool word fiber20 32 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_32_12)
    (by decide) (by decide)
    (by simpa [cert20_move_32_12] using cert20_component_32_12_eq)
    (by decide) (by decide) (by decide)

def cert20_move_33_13 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_33_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_33_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_33_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_33_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 33 [])
      LColor.b LColor.p cert20_seen_33_13_0 = cert20_layer_33_13_0 := by
  decide

def cert20_seen_33_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_33_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_33_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 33 [])
      LColor.b LColor.p cert20_seen_33_13_1 = cert20_layer_33_13_1 := by
  decide

def cert20_seen_33_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_33_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_33_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 33 [])
      LColor.b LColor.p cert20_seen_33_13_2 = cert20_layer_33_13_2 := by
  decide

def cert20_seen_33_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_33_13_3 : List ChainEdge :=
  []

theorem cert20_layer_33_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 33 [])
      LColor.b LColor.p cert20_seen_33_13_3 = cert20_layer_33_13_3 := by
  decide

theorem cert20_component_33_13_eq :
    closedCollarComponent word (listGetD fiber20 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_33_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 33 [])
      LColor.b LColor.p 27 cert20_seen_33_13_0 = cert20_component_33_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 33 []) LColor.b LColor.p
    cert20_seen_33_13_0 cert20_layer_33_13_0 26 cert20_layer_33_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 33 [])
      LColor.b LColor.p 26 cert20_seen_33_13_1 = cert20_component_33_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 33 []) LColor.b LColor.p
    cert20_seen_33_13_1 cert20_layer_33_13_1 25 cert20_layer_33_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 33 [])
      LColor.b LColor.p 25 cert20_seen_33_13_2 = cert20_component_33_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 33 []) LColor.b LColor.p
    cert20_seen_33_13_2 cert20_layer_33_13_2 24 cert20_layer_33_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 33 [])
      LColor.b LColor.p 24 cert20_seen_33_13_3 = cert20_component_33_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 33 []) LColor.b LColor.p
    cert20_seen_33_13_3 cert20_layer_33_13_3_eq 24

theorem cert20_step_33_13 :
    closedCollarIndexStepBool word fiber20 33 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_33_13)
    (by decide) (by decide)
    (by simpa [cert20_move_33_13] using cert20_component_33_13_eq)
    (by decide) (by decide) (by decide)

def cert20_move_34_14 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_34_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_34_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_34_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_34_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 34 [])
      LColor.b LColor.p cert20_seen_34_14_0 = cert20_layer_34_14_0 := by
  decide

def cert20_seen_34_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_34_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_34_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 34 [])
      LColor.b LColor.p cert20_seen_34_14_1 = cert20_layer_34_14_1 := by
  decide

def cert20_seen_34_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_34_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_34_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 34 [])
      LColor.b LColor.p cert20_seen_34_14_2 = cert20_layer_34_14_2 := by
  decide

def cert20_seen_34_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_34_14_3 : List ChainEdge :=
  []

theorem cert20_layer_34_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 34 [])
      LColor.b LColor.p cert20_seen_34_14_3 = cert20_layer_34_14_3 := by
  decide

theorem cert20_component_34_14_eq :
    closedCollarComponent word (listGetD fiber20 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_34_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 34 [])
      LColor.b LColor.p 27 cert20_seen_34_14_0 = cert20_component_34_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 34 []) LColor.b LColor.p
    cert20_seen_34_14_0 cert20_layer_34_14_0 26 cert20_layer_34_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 34 [])
      LColor.b LColor.p 26 cert20_seen_34_14_1 = cert20_component_34_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 34 []) LColor.b LColor.p
    cert20_seen_34_14_1 cert20_layer_34_14_1 25 cert20_layer_34_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 34 [])
      LColor.b LColor.p 25 cert20_seen_34_14_2 = cert20_component_34_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 34 []) LColor.b LColor.p
    cert20_seen_34_14_2 cert20_layer_34_14_2 24 cert20_layer_34_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 34 [])
      LColor.b LColor.p 24 cert20_seen_34_14_3 = cert20_component_34_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 34 []) LColor.b LColor.p
    cert20_seen_34_14_3 cert20_layer_34_14_3_eq 24

theorem cert20_step_34_14 :
    closedCollarIndexStepBool word fiber20 34 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_34_14)
    (by decide) (by decide)
    (by simpa [cert20_move_34_14] using cert20_component_34_14_eq)
    (by decide) (by decide) (by decide)

def cert20_move_35_15 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_35_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_35_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_35_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_35_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 35 [])
      LColor.b LColor.p cert20_seen_35_15_0 = cert20_layer_35_15_0 := by
  decide

def cert20_seen_35_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_35_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_35_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 35 [])
      LColor.b LColor.p cert20_seen_35_15_1 = cert20_layer_35_15_1 := by
  decide

def cert20_seen_35_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_35_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_35_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 35 [])
      LColor.b LColor.p cert20_seen_35_15_2 = cert20_layer_35_15_2 := by
  decide

def cert20_seen_35_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_35_15_3 : List ChainEdge :=
  []

theorem cert20_layer_35_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 35 [])
      LColor.b LColor.p cert20_seen_35_15_3 = cert20_layer_35_15_3 := by
  decide

theorem cert20_component_35_15_eq :
    closedCollarComponent word (listGetD fiber20 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_35_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 35 [])
      LColor.b LColor.p 27 cert20_seen_35_15_0 = cert20_component_35_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 35 []) LColor.b LColor.p
    cert20_seen_35_15_0 cert20_layer_35_15_0 26 cert20_layer_35_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 35 [])
      LColor.b LColor.p 26 cert20_seen_35_15_1 = cert20_component_35_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 35 []) LColor.b LColor.p
    cert20_seen_35_15_1 cert20_layer_35_15_1 25 cert20_layer_35_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 35 [])
      LColor.b LColor.p 25 cert20_seen_35_15_2 = cert20_component_35_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 35 []) LColor.b LColor.p
    cert20_seen_35_15_2 cert20_layer_35_15_2 24 cert20_layer_35_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 35 [])
      LColor.b LColor.p 24 cert20_seen_35_15_3 = cert20_component_35_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 35 []) LColor.b LColor.p
    cert20_seen_35_15_3 cert20_layer_35_15_3_eq 24

theorem cert20_step_35_15 :
    closedCollarIndexStepBool word fiber20 35 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_35_15)
    (by decide) (by decide)
    (by simpa [cert20_move_35_15] using cert20_component_35_15_eq)
    (by decide) (by decide) (by decide)

def cert20_move_36_16 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_36_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_36_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_36_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_36_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 36 [])
      LColor.b LColor.p cert20_seen_36_16_0 = cert20_layer_36_16_0 := by
  decide

def cert20_seen_36_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_36_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_36_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 36 [])
      LColor.b LColor.p cert20_seen_36_16_1 = cert20_layer_36_16_1 := by
  decide

def cert20_seen_36_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_36_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_36_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 36 [])
      LColor.b LColor.p cert20_seen_36_16_2 = cert20_layer_36_16_2 := by
  decide

def cert20_seen_36_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_36_16_3 : List ChainEdge :=
  []

theorem cert20_layer_36_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 36 [])
      LColor.b LColor.p cert20_seen_36_16_3 = cert20_layer_36_16_3 := by
  decide

theorem cert20_component_36_16_eq :
    closedCollarComponent word (listGetD fiber20 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_36_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 36 [])
      LColor.b LColor.p 27 cert20_seen_36_16_0 = cert20_component_36_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 36 []) LColor.b LColor.p
    cert20_seen_36_16_0 cert20_layer_36_16_0 26 cert20_layer_36_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 36 [])
      LColor.b LColor.p 26 cert20_seen_36_16_1 = cert20_component_36_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 36 []) LColor.b LColor.p
    cert20_seen_36_16_1 cert20_layer_36_16_1 25 cert20_layer_36_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 36 [])
      LColor.b LColor.p 25 cert20_seen_36_16_2 = cert20_component_36_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 36 []) LColor.b LColor.p
    cert20_seen_36_16_2 cert20_layer_36_16_2 24 cert20_layer_36_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 36 [])
      LColor.b LColor.p 24 cert20_seen_36_16_3 = cert20_component_36_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 36 []) LColor.b LColor.p
    cert20_seen_36_16_3 cert20_layer_36_16_3_eq 24

theorem cert20_step_36_16 :
    closedCollarIndexStepBool word fiber20 36 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_36_16)
    (by decide) (by decide)
    (by simpa [cert20_move_36_16] using cert20_component_36_16_eq)
    (by decide) (by decide) (by decide)

def cert20_move_37_17 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_37_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_seen_37_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_37_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_37_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 37 [])
      LColor.b LColor.p cert20_seen_37_17_0 = cert20_layer_37_17_0 := by
  decide

def cert20_seen_37_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_37_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_37_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 37 [])
      LColor.b LColor.p cert20_seen_37_17_1 = cert20_layer_37_17_1 := by
  decide

def cert20_seen_37_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_37_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert20_layer_37_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 37 [])
      LColor.b LColor.p cert20_seen_37_17_2 = cert20_layer_37_17_2 := by
  decide

def cert20_seen_37_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert20_layer_37_17_3 : List ChainEdge :=
  []

theorem cert20_layer_37_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 37 [])
      LColor.b LColor.p cert20_seen_37_17_3 = cert20_layer_37_17_3 := by
  decide

theorem cert20_component_37_17_eq :
    closedCollarComponent word (listGetD fiber20 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_37_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 37 [])
      LColor.b LColor.p 27 cert20_seen_37_17_0 = cert20_component_37_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 37 []) LColor.b LColor.p
    cert20_seen_37_17_0 cert20_layer_37_17_0 26 cert20_layer_37_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 37 [])
      LColor.b LColor.p 26 cert20_seen_37_17_1 = cert20_component_37_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 37 []) LColor.b LColor.p
    cert20_seen_37_17_1 cert20_layer_37_17_1 25 cert20_layer_37_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 37 [])
      LColor.b LColor.p 25 cert20_seen_37_17_2 = cert20_component_37_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 37 []) LColor.b LColor.p
    cert20_seen_37_17_2 cert20_layer_37_17_2 24 cert20_layer_37_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 37 [])
      LColor.b LColor.p 24 cert20_seen_37_17_3 = cert20_component_37_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 37 []) LColor.b LColor.p
    cert20_seen_37_17_3 cert20_layer_37_17_3_eq 24

theorem cert20_step_37_17 :
    closedCollarIndexStepBool word fiber20 37 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_37_17)
    (by decide) (by decide)
    (by simpa [cert20_move_37_17] using cert20_component_37_17_eq)
    (by decide) (by decide) (by decide)

def cert20_move_38_27 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_38_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_seen_38_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_38_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_38_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_0 = cert20_layer_38_27_0 := by
  decide

def cert20_seen_38_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_38_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_38_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_1 = cert20_layer_38_27_1 := by
  decide

def cert20_seen_38_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_38_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_38_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_2 = cert20_layer_38_27_2 := by
  decide

def cert20_seen_38_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_38_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert20_layer_38_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_3 = cert20_layer_38_27_3 := by
  decide

def cert20_seen_38_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert20_layer_38_27_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert20_layer_38_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_4 = cert20_layer_38_27_4 := by
  decide

def cert20_seen_38_27_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_38_27_5 : List ChainEdge :=
  []

theorem cert20_layer_38_27_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 38 [])
      LColor.r LColor.p cert20_seen_38_27_5 = cert20_layer_38_27_5 := by
  decide

theorem cert20_component_38_27_eq :
    closedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_38_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 27 cert20_seen_38_27_0 = cert20_component_38_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_0 cert20_layer_38_27_0 26 cert20_layer_38_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 26 cert20_seen_38_27_1 = cert20_component_38_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_1 cert20_layer_38_27_1 25 cert20_layer_38_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 25 cert20_seen_38_27_2 = cert20_component_38_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_2 cert20_layer_38_27_2 24 cert20_layer_38_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 24 cert20_seen_38_27_3 = cert20_component_38_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_3 cert20_layer_38_27_3 23 cert20_layer_38_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 23 cert20_seen_38_27_4 = cert20_component_38_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_4 cert20_layer_38_27_4 22 cert20_layer_38_27_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 38 [])
      LColor.r LColor.p 22 cert20_seen_38_27_5 = cert20_component_38_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 38 []) LColor.r LColor.p
    cert20_seen_38_27_5 cert20_layer_38_27_5_eq 22

theorem cert20_step_38_27 :
    closedCollarIndexStepBool word fiber20 38 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_38_27)
    (by decide) (by decide)
    (by simpa [cert20_move_38_27] using cert20_component_38_27_eq)
    (by decide) (by decide) (by decide)

def cert20_move_39_26 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_39_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_seen_39_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_39_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_39_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_0 = cert20_layer_39_26_0 := by
  decide

def cert20_seen_39_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_39_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert20_layer_39_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_1 = cert20_layer_39_26_1 := by
  decide

def cert20_seen_39_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert20_layer_39_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert20_layer_39_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_2 = cert20_layer_39_26_2 := by
  decide

def cert20_seen_39_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert20_layer_39_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert20_layer_39_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_3 = cert20_layer_39_26_3 := by
  decide

def cert20_seen_39_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert20_layer_39_26_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert20_layer_39_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_4 = cert20_layer_39_26_4 := by
  decide

def cert20_seen_39_26_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert20_layer_39_26_5 : List ChainEdge :=
  []

theorem cert20_layer_39_26_5_eq :
    closedCollarComponentLayer word (listGetD fiber20 39 [])
      LColor.r LColor.p cert20_seen_39_26_5 = cert20_layer_39_26_5 := by
  decide

theorem cert20_component_39_26_eq :
    closedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_39_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 27 cert20_seen_39_26_0 = cert20_component_39_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_0 cert20_layer_39_26_0 26 cert20_layer_39_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 26 cert20_seen_39_26_1 = cert20_component_39_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_1 cert20_layer_39_26_1 25 cert20_layer_39_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 25 cert20_seen_39_26_2 = cert20_component_39_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_2 cert20_layer_39_26_2 24 cert20_layer_39_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 24 cert20_seen_39_26_3 = cert20_component_39_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_3 cert20_layer_39_26_3 23 cert20_layer_39_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 23 cert20_seen_39_26_4 = cert20_component_39_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_4 cert20_layer_39_26_4 22 cert20_layer_39_26_4_eq]
  change closeClosedCollarComponent word (listGetD fiber20 39 [])
      LColor.r LColor.p 22 cert20_seen_39_26_5 = cert20_component_39_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 39 []) LColor.r LColor.p
    cert20_seen_39_26_5 cert20_layer_39_26_5_eq 22

theorem cert20_step_39_26 :
    closedCollarIndexStepBool word fiber20 39 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_39_26)
    (by decide) (by decide)
    (by simpa [cert20_move_39_26] using cert20_component_39_26_eq)
    (by decide) (by decide) (by decide)

def cert20_move_40_20 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_40_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_40_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_40_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_40_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 40 [])
      LColor.b LColor.p cert20_seen_40_20_0 = cert20_layer_40_20_0 := by
  decide

def cert20_seen_40_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_40_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_40_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 40 [])
      LColor.b LColor.p cert20_seen_40_20_1 = cert20_layer_40_20_1 := by
  decide

def cert20_seen_40_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_40_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_40_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 40 [])
      LColor.b LColor.p cert20_seen_40_20_2 = cert20_layer_40_20_2 := by
  decide

def cert20_seen_40_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_40_20_3 : List ChainEdge :=
  []

theorem cert20_layer_40_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 40 [])
      LColor.b LColor.p cert20_seen_40_20_3 = cert20_layer_40_20_3 := by
  decide

theorem cert20_component_40_20_eq :
    closedCollarComponent word (listGetD fiber20 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_40_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 40 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 40 [])
      LColor.b LColor.p 27 cert20_seen_40_20_0 = cert20_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 40 []) LColor.b LColor.p
    cert20_seen_40_20_0 cert20_layer_40_20_0 26 cert20_layer_40_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 40 [])
      LColor.b LColor.p 26 cert20_seen_40_20_1 = cert20_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 40 []) LColor.b LColor.p
    cert20_seen_40_20_1 cert20_layer_40_20_1 25 cert20_layer_40_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 40 [])
      LColor.b LColor.p 25 cert20_seen_40_20_2 = cert20_component_40_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 40 []) LColor.b LColor.p
    cert20_seen_40_20_2 cert20_layer_40_20_2 24 cert20_layer_40_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 40 [])
      LColor.b LColor.p 24 cert20_seen_40_20_3 = cert20_component_40_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 40 []) LColor.b LColor.p
    cert20_seen_40_20_3 cert20_layer_40_20_3_eq 24

theorem cert20_step_40_20 :
    closedCollarIndexStepBool word fiber20 40 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_40_20)
    (by decide) (by decide)
    (by simpa [cert20_move_40_20] using cert20_component_40_20_eq)
    (by decide) (by decide) (by decide)

def cert20_move_41_21 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert20_component_41_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_seen_41_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert20_layer_41_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert20_layer_41_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 41 [])
      LColor.b LColor.p cert20_seen_41_21_0 = cert20_layer_41_21_0 := by
  decide

def cert20_seen_41_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert20_layer_41_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert20_layer_41_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 41 [])
      LColor.b LColor.p cert20_seen_41_21_1 = cert20_layer_41_21_1 := by
  decide

def cert20_seen_41_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert20_layer_41_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert20_layer_41_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 41 [])
      LColor.b LColor.p cert20_seen_41_21_2 = cert20_layer_41_21_2 := by
  decide

def cert20_seen_41_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert20_layer_41_21_3 : List ChainEdge :=
  []

theorem cert20_layer_41_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 41 [])
      LColor.b LColor.p cert20_seen_41_21_3 = cert20_layer_41_21_3 := by
  decide

theorem cert20_component_41_21_eq :
    closedCollarComponent word (listGetD fiber20 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert20_component_41_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 41 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 41 [])
      LColor.b LColor.p 27 cert20_seen_41_21_0 = cert20_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 41 []) LColor.b LColor.p
    cert20_seen_41_21_0 cert20_layer_41_21_0 26 cert20_layer_41_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 41 [])
      LColor.b LColor.p 26 cert20_seen_41_21_1 = cert20_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 41 []) LColor.b LColor.p
    cert20_seen_41_21_1 cert20_layer_41_21_1 25 cert20_layer_41_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 41 [])
      LColor.b LColor.p 25 cert20_seen_41_21_2 = cert20_component_41_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 41 []) LColor.b LColor.p
    cert20_seen_41_21_2 cert20_layer_41_21_2 24 cert20_layer_41_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 41 [])
      LColor.b LColor.p 24 cert20_seen_41_21_3 = cert20_component_41_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 41 []) LColor.b LColor.p
    cert20_seen_41_21_3 cert20_layer_41_21_3_eq 24

theorem cert20_step_41_21 :
    closedCollarIndexStepBool word fiber20 41 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_41_21)
    (by decide) (by decide)
    (by simpa [cert20_move_41_21] using cert20_component_41_21_eq)
    (by decide) (by decide) (by decide)

def cert20_move_42_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_42_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_42_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_42_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_42_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 42 [])
      LColor.r LColor.p cert20_seen_42_24_0 = cert20_layer_42_24_0 := by
  decide

def cert20_seen_42_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_42_24_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_42_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 42 [])
      LColor.r LColor.p cert20_seen_42_24_1 = cert20_layer_42_24_1 := by
  decide

def cert20_seen_42_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_42_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_42_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 42 [])
      LColor.r LColor.p cert20_seen_42_24_2 = cert20_layer_42_24_2 := by
  decide

def cert20_seen_42_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_42_24_3 : List ChainEdge :=
  []

theorem cert20_layer_42_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 42 [])
      LColor.r LColor.p cert20_seen_42_24_3 = cert20_layer_42_24_3 := by
  decide

theorem cert20_component_42_24_eq :
    closedCollarComponent word (listGetD fiber20 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_42_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 42 [])
      LColor.r LColor.p 27 cert20_seen_42_24_0 = cert20_component_42_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 42 []) LColor.r LColor.p
    cert20_seen_42_24_0 cert20_layer_42_24_0 26 cert20_layer_42_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 42 [])
      LColor.r LColor.p 26 cert20_seen_42_24_1 = cert20_component_42_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 42 []) LColor.r LColor.p
    cert20_seen_42_24_1 cert20_layer_42_24_1 25 cert20_layer_42_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 42 [])
      LColor.r LColor.p 25 cert20_seen_42_24_2 = cert20_component_42_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 42 []) LColor.r LColor.p
    cert20_seen_42_24_2 cert20_layer_42_24_2 24 cert20_layer_42_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 42 [])
      LColor.r LColor.p 24 cert20_seen_42_24_3 = cert20_component_42_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 42 []) LColor.r LColor.p
    cert20_seen_42_24_3 cert20_layer_42_24_3_eq 24

theorem cert20_step_42_24 :
    closedCollarIndexStepBool word fiber20 42 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_42_24)
    (by decide) (by decide)
    (by simpa [cert20_move_42_24] using cert20_component_42_24_eq)
    (by decide) (by decide) (by decide)

def cert20_move_43_25 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert20_component_43_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_seen_43_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert20_layer_43_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert20_layer_43_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber20 43 [])
      LColor.r LColor.p cert20_seen_43_25_0 = cert20_layer_43_25_0 := by
  decide

def cert20_seen_43_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert20_layer_43_25_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert20_layer_43_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber20 43 [])
      LColor.r LColor.p cert20_seen_43_25_1 = cert20_layer_43_25_1 := by
  decide

def cert20_seen_43_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert20_layer_43_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert20_layer_43_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber20 43 [])
      LColor.r LColor.p cert20_seen_43_25_2 = cert20_layer_43_25_2 := by
  decide

def cert20_seen_43_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert20_layer_43_25_3 : List ChainEdge :=
  []

theorem cert20_layer_43_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber20 43 [])
      LColor.r LColor.p cert20_seen_43_25_3 = cert20_layer_43_25_3 := by
  decide

theorem cert20_component_43_25_eq :
    closedCollarComponent word (listGetD fiber20 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert20_component_43_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber20 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber20 43 [])
      LColor.r LColor.p 27 cert20_seen_43_25_0 = cert20_component_43_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 43 []) LColor.r LColor.p
    cert20_seen_43_25_0 cert20_layer_43_25_0 26 cert20_layer_43_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber20 43 [])
      LColor.r LColor.p 26 cert20_seen_43_25_1 = cert20_component_43_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 43 []) LColor.r LColor.p
    cert20_seen_43_25_1 cert20_layer_43_25_1 25 cert20_layer_43_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber20 43 [])
      LColor.r LColor.p 25 cert20_seen_43_25_2 = cert20_component_43_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber20 43 []) LColor.r LColor.p
    cert20_seen_43_25_2 cert20_layer_43_25_2 24 cert20_layer_43_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber20 43 [])
      LColor.r LColor.p 24 cert20_seen_43_25_3 = cert20_component_43_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber20 43 []) LColor.r LColor.p
    cert20_seen_43_25_3 cert20_layer_43_25_3_eq 24

theorem cert20_step_43_25 :
    closedCollarIndexStepBool word fiber20 43 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert20_move_43_25)
    (by decide) (by decide)
    (by simpa [cert20_move_43_25] using cert20_component_43_25_eq)
    (by decide) (by decide) (by decide)

theorem cert20_row_0 :
    closedCollarParentIndexValid word fiber20 cert20.parents 0 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length]

theorem cert20_row_1 :
    closedCollarParentIndexValid word fiber20 cert20.parents 1 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_1_0, cert20_step_0_1]

theorem cert20_row_2 :
    closedCollarParentIndexValid word fiber20 cert20.parents 2 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_2_0, cert20_step_0_2]

theorem cert20_row_3 :
    closedCollarParentIndexValid word fiber20 cert20.parents 3 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_3_1, cert20_step_1_3]

theorem cert20_row_4 :
    closedCollarParentIndexValid word fiber20 cert20.parents 4 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_4_1, cert20_step_1_4]

theorem cert20_row_5 :
    closedCollarParentIndexValid word fiber20 cert20.parents 5 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_5_0, cert20_step_0_5]

theorem cert20_row_6 :
    closedCollarParentIndexValid word fiber20 cert20.parents 6 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_6_0, cert20_step_0_6]

theorem cert20_row_7 :
    closedCollarParentIndexValid word fiber20 cert20.parents 7 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_7_1, cert20_step_1_7]

theorem cert20_row_8 :
    closedCollarParentIndexValid word fiber20 cert20.parents 8 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_8_2, cert20_step_2_8]

theorem cert20_row_9 :
    closedCollarParentIndexValid word fiber20 cert20.parents 9 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_9_3, cert20_step_3_9]

theorem cert20_row_10 :
    closedCollarParentIndexValid word fiber20 cert20.parents 10 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_10_4, cert20_step_4_10]

theorem cert20_row_11 :
    closedCollarParentIndexValid word fiber20 cert20.parents 11 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_11_5, cert20_step_5_11]

theorem cert20_row_12 :
    closedCollarParentIndexValid word fiber20 cert20.parents 12 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_12_0, cert20_step_0_12]

theorem cert20_row_13 :
    closedCollarParentIndexValid word fiber20 cert20.parents 13 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_13_1, cert20_step_1_13]

theorem cert20_row_14 :
    closedCollarParentIndexValid word fiber20 cert20.parents 14 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_14_2, cert20_step_2_14]

theorem cert20_row_15 :
    closedCollarParentIndexValid word fiber20 cert20.parents 15 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_15_3, cert20_step_3_15]

theorem cert20_row_16 :
    closedCollarParentIndexValid word fiber20 cert20.parents 16 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_16_4, cert20_step_4_16]

theorem cert20_row_17 :
    closedCollarParentIndexValid word fiber20 cert20.parents 17 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_17_5, cert20_step_5_17]

theorem cert20_row_18 :
    closedCollarParentIndexValid word fiber20 cert20.parents 18 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_18_6, cert20_step_6_18]

theorem cert20_row_19 :
    closedCollarParentIndexValid word fiber20 cert20.parents 19 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_19_7, cert20_step_7_19]

theorem cert20_row_20 :
    closedCollarParentIndexValid word fiber20 cert20.parents 20 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_20_8, cert20_step_8_20]

theorem cert20_row_21 :
    closedCollarParentIndexValid word fiber20 cert20.parents 21 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_21_9, cert20_step_9_21]

theorem cert20_row_22 :
    closedCollarParentIndexValid word fiber20 cert20.parents 22 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_22_10, cert20_step_10_22]

theorem cert20_row_23 :
    closedCollarParentIndexValid word fiber20 cert20.parents 23 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_23_11, cert20_step_11_23]

theorem cert20_row_24 :
    closedCollarParentIndexValid word fiber20 cert20.parents 24 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_24_2, cert20_step_2_24]

theorem cert20_row_25 :
    closedCollarParentIndexValid word fiber20 cert20.parents 25 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_25_3, cert20_step_3_25]

theorem cert20_row_26 :
    closedCollarParentIndexValid word fiber20 cert20.parents 26 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_26_4, cert20_step_4_26]

theorem cert20_row_27 :
    closedCollarParentIndexValid word fiber20 cert20.parents 27 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_27_5, cert20_step_5_27]

theorem cert20_row_28 :
    closedCollarParentIndexValid word fiber20 cert20.parents 28 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_28_8, cert20_step_8_28]

theorem cert20_row_29 :
    closedCollarParentIndexValid word fiber20 cert20.parents 29 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_29_9, cert20_step_9_29]

theorem cert20_row_30 :
    closedCollarParentIndexValid word fiber20 cert20.parents 30 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_30_10, cert20_step_10_30]

theorem cert20_row_31 :
    closedCollarParentIndexValid word fiber20 cert20.parents 31 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_31_11, cert20_step_11_31]

theorem cert20_row_32 :
    closedCollarParentIndexValid word fiber20 cert20.parents 32 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_32_12, cert20_step_12_32]

theorem cert20_row_33 :
    closedCollarParentIndexValid word fiber20 cert20.parents 33 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_33_13, cert20_step_13_33]

theorem cert20_row_34 :
    closedCollarParentIndexValid word fiber20 cert20.parents 34 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_34_14, cert20_step_14_34]

theorem cert20_row_35 :
    closedCollarParentIndexValid word fiber20 cert20.parents 35 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_35_15, cert20_step_15_35]

theorem cert20_row_36 :
    closedCollarParentIndexValid word fiber20 cert20.parents 36 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_36_16, cert20_step_16_36]

theorem cert20_row_37 :
    closedCollarParentIndexValid word fiber20 cert20.parents 37 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_37_17, cert20_step_17_37]

theorem cert20_row_38 :
    closedCollarParentIndexValid word fiber20 cert20.parents 38 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_38_27, cert20_step_27_38]

theorem cert20_row_39 :
    closedCollarParentIndexValid word fiber20 cert20.parents 39 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_39_26, cert20_step_26_39]

theorem cert20_row_40 :
    closedCollarParentIndexValid word fiber20 cert20.parents 40 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_40_20, cert20_step_20_40]

theorem cert20_row_41 :
    closedCollarParentIndexValid word fiber20 cert20.parents 41 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_41_21, cert20_step_21_41]

theorem cert20_row_42 :
    closedCollarParentIndexValid word fiber20 cert20.parents 42 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_42_24, cert20_step_24_42]

theorem cert20_row_43 :
    closedCollarParentIndexValid word fiber20 cert20.parents 43 = true := by
  have cert20_fiber_length : fiber20.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert20, listGetD, cert20_fiber_length, cert20_step_43_25, cert20_step_25_43]

theorem cert20_rows :
    closedCollarSpineRowsValid word fiber20 cert20.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert20_fiber_length : fiber20.length = 44 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert20_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert20_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert20_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert20_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert20_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert20_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert20_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert20_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert20_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert20_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert20_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert20_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert20_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert20_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert20_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert20_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert20_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert20_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert20_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert20_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert20_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert20_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert20_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert20_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert20_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert20_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert20_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert20_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert20_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert20_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert20_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert20_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert20_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert20_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert20_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert20_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert20_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert20_row_43
  · omega

theorem cert20_root :
    closedCollarSpineParentsReachRoot fiber20 cert20 = true := by
  decide

theorem cert20_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.p] := by
  change closedCollarFiberKempeConnected word cert20.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert20 fiber20_eq cert20_rows cert20_root


end GoertzelLemma818ClosedCollarS2Word11
end Mettapedia.GraphTheory.FourColor
