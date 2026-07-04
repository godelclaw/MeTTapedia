import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word4

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast44 : List TauState :=
  [stateAt 32, stateAt 40, stateAt 48, stateAt 56, stateAt 132, stateAt 140, stateAt 148, stateAt 156]

theorem keyedLast44_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.p, LColor.p]) =
      keyedLast44 := by
  decide

def fiber44OuterChunks : List (List (List TauState)) :=
[
  []
, []
, []
, []
, []
, []
, []
, []
, []
, [
  [stateAt 148, stateAt 148, stateAt 148]
, [stateAt 148, stateAt 149, stateAt 156]
, [stateAt 148, stateAt 150, stateAt 48]
, [stateAt 148, stateAt 151, stateAt 56]
, [stateAt 148, stateAt 164, stateAt 132]
, [stateAt 148, stateAt 165, stateAt 140]
, [stateAt 149, stateAt 156, stateAt 148]
, [stateAt 149, stateAt 157, stateAt 156]
, [stateAt 149, stateAt 158, stateAt 48]
, [stateAt 149, stateAt 159, stateAt 56]
, [stateAt 149, stateAt 172, stateAt 132]
, [stateAt 149, stateAt 173, stateAt 140]
, [stateAt 150, stateAt 2, stateAt 32]
, [stateAt 150, stateAt 3, stateAt 40]
, [stateAt 150, stateAt 48, stateAt 148]
, [stateAt 150, stateAt 49, stateAt 156]
, [stateAt 150, stateAt 50, stateAt 48]
, [stateAt 150, stateAt 51, stateAt 56]
, [stateAt 151, stateAt 10, stateAt 32]
, [stateAt 151, stateAt 11, stateAt 40]
, [stateAt 151, stateAt 56, stateAt 148]
, [stateAt 151, stateAt 57, stateAt 156]
, [stateAt 151, stateAt 58, stateAt 48]
, [stateAt 151, stateAt 59, stateAt 56]
]
, [
  [stateAt 164, stateAt 132, stateAt 148]
, [stateAt 164, stateAt 133, stateAt 156]
, [stateAt 164, stateAt 134, stateAt 48]
, [stateAt 164, stateAt 135, stateAt 56]
, [stateAt 164, stateAt 180, stateAt 132]
, [stateAt 164, stateAt 181, stateAt 140]
, [stateAt 165, stateAt 140, stateAt 148]
, [stateAt 165, stateAt 141, stateAt 156]
, [stateAt 165, stateAt 142, stateAt 48]
, [stateAt 165, stateAt 143, stateAt 56]
, [stateAt 165, stateAt 188, stateAt 132]
, [stateAt 165, stateAt 189, stateAt 140]
, [stateAt 166, stateAt 66, stateAt 32]
, [stateAt 166, stateAt 67, stateAt 40]
, [stateAt 166, stateAt 116, stateAt 132]
, [stateAt 166, stateAt 117, stateAt 140]
, [stateAt 167, stateAt 74, stateAt 32]
, [stateAt 167, stateAt 75, stateAt 40]
, [stateAt 167, stateAt 124, stateAt 132]
, [stateAt 167, stateAt 125, stateAt 140]
]
, []
]

def fiber44 : List (List TauState) :=
  fiber44OuterChunks.flatten

theorem fiber44_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 0 []) =
      listGetD fiber44OuterChunks 0 [] := by
  decide

theorem fiber44_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 1 []) =
      listGetD fiber44OuterChunks 1 [] := by
  decide

theorem fiber44_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 2 []) =
      listGetD fiber44OuterChunks 2 [] := by
  decide

theorem fiber44_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 3 []) =
      listGetD fiber44OuterChunks 3 [] := by
  decide

theorem fiber44_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 4 []) =
      listGetD fiber44OuterChunks 4 [] := by
  decide

theorem fiber44_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 5 []) =
      listGetD fiber44OuterChunks 5 [] := by
  decide

theorem fiber44_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 6 []) =
      listGetD fiber44OuterChunks 6 [] := by
  decide

theorem fiber44_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 7 []) =
      listGetD fiber44OuterChunks 7 [] := by
  decide

theorem fiber44_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 8 []) =
      listGetD fiber44OuterChunks 8 [] := by
  decide

theorem fiber44_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 9 []) =
      listGetD fiber44OuterChunks 9 [] := by
  decide

theorem fiber44_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 10 []) =
      listGetD fiber44OuterChunks 10 [] := by
  decide

theorem fiber44_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks 11 []) =
      listGetD fiber44OuterChunks 11 [] := by
  decide

theorem fiber44_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast44
        (listGetD tauStateChunks idx []) =
      listGetD fiber44OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber44_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber44_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber44_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber44_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber44_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber44_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber44_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber44_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber44_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber44_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber44_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber44_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber44_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast44 =
      fiber44 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast44 tauStateChunks fiber44OuterChunks
    tauStateChunks_eq (by rfl) fiber44_outer_get
  simpa [fiber44] using h

theorem fiber44_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.p, LColor.p] = fiber44 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.p, LColor.p] keyedLast44_eq
  exact hfrom.trans fiber44_keyedFrom_eq

theorem fiber44_eq :
    closedCollarFiber word [LColor.b, LColor.b, LColor.p, LColor.p] = fiber44 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.normal [LColor.b, LColor.b, LColor.p, LColor.p]
  exact hfast.trans fiber44_keyed_eq

def cert44 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.p, LColor.p],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 1, 0, 0, 1, 0, 1, 2, 3, 4, 5, 10, 11, 6, 7, 8, 9, 4, 5, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 26, 27, 28, 29, 18, 19, 20, 21] }

def cert44_move_0_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert44_component_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert44_layer_0_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_0_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_1_0 = cert44_layer_0_1_0 := by
  decide

def cert44_seen_0_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_0_1_1 : List ChainEdge :=
  []

theorem cert44_layer_0_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_1_1 = cert44_layer_0_1_1 := by
  decide

theorem cert44_component_0_1_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert44_component_0_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 27 cert44_seen_0_1_0 = cert44_component_0_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_1_0 cert44_layer_0_1_0 26 cert44_layer_0_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 26 cert44_seen_0_1_1 = cert44_component_0_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_1_1 cert44_layer_0_1_1_eq 26

theorem cert44_step_0_1 :
    closedCollarIndexStepBool word fiber44 0 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_1)
    (by decide) (by decide)
    (by simpa [cert44_move_0_1] using cert44_component_0_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert44_component_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_seen_0_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_0_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_0_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_3_0 = cert44_layer_0_3_0 := by
  decide

def cert44_seen_0_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_0_3_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_0_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_3_1 = cert44_layer_0_3_1 := by
  decide

def cert44_seen_0_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_0_3_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_0_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_3_2 = cert44_layer_0_3_2 := by
  decide

def cert44_seen_0_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_0_3_3 : List ChainEdge :=
  []

theorem cert44_layer_0_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_3_3 = cert44_layer_0_3_3 := by
  decide

theorem cert44_component_0_3_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert44_component_0_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 27 cert44_seen_0_3_0 = cert44_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_3_0 cert44_layer_0_3_0 26 cert44_layer_0_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 26 cert44_seen_0_3_1 = cert44_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_3_1 cert44_layer_0_3_1 25 cert44_layer_0_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 25 cert44_seen_0_3_2 = cert44_component_0_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_3_2 cert44_layer_0_3_2 24 cert44_layer_0_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 24 cert44_seen_0_3_3 = cert44_component_0_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_3_3 cert44_layer_0_3_3_eq 24

theorem cert44_step_0_3 :
    closedCollarIndexStepBool word fiber44 0 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_3)
    (by decide) (by decide)
    (by simpa [cert44_move_0_3] using cert44_component_0_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert44_component_0_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_seen_0_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_0_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_0_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_4_0 = cert44_layer_0_4_0 := by
  decide

def cert44_seen_0_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_0_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_0_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_4_1 = cert44_layer_0_4_1 := by
  decide

def cert44_seen_0_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_0_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_0_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_4_2 = cert44_layer_0_4_2 := by
  decide

def cert44_seen_0_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_0_4_3 : List ChainEdge :=
  []

theorem cert44_layer_0_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_4_3 = cert44_layer_0_4_3 := by
  decide

theorem cert44_component_0_4_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert44_component_0_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 27 cert44_seen_0_4_0 = cert44_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_4_0 cert44_layer_0_4_0 26 cert44_layer_0_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 26 cert44_seen_0_4_1 = cert44_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_4_1 cert44_layer_0_4_1 25 cert44_layer_0_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 25 cert44_seen_0_4_2 = cert44_component_0_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_4_2 cert44_layer_0_4_2 24 cert44_layer_0_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 24 cert44_seen_0_4_3 = cert44_component_0_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_4_3 cert44_layer_0_4_3_eq 24

theorem cert44_step_0_4 :
    closedCollarIndexStepBool word fiber44 0 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_4)
    (by decide) (by decide)
    (by simpa [cert44_move_0_4] using cert44_component_0_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_6 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_6_0 = cert44_layer_0_6_0 := by
  decide

def cert44_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_0_6_1 : List ChainEdge :=
  []

theorem cert44_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_6_1 = cert44_layer_0_6_1 := by
  decide

theorem cert44_component_0_6_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 27 cert44_seen_0_6_0 = cert44_component_0_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_6_0 cert44_layer_0_6_0 26 cert44_layer_0_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p 26 cert44_seen_0_6_1 = cert44_component_0_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.b LColor.p
    cert44_seen_0_6_1 cert44_layer_0_6_1_eq 26

theorem cert44_step_0_6 :
    closedCollarIndexStepBool word fiber44 0 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_6)
    (by decide) (by decide)
    (by simpa [cert44_move_0_6] using cert44_component_0_6_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_20 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_0_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_0_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_0_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_0_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_20_0 = cert44_layer_0_20_0 := by
  decide

def cert44_seen_0_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_0_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_0_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_20_1 = cert44_layer_0_20_1 := by
  decide

def cert44_seen_0_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_0_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_0_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_20_2 = cert44_layer_0_20_2 := by
  decide

def cert44_seen_0_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_0_20_3 : List ChainEdge :=
  []

theorem cert44_layer_0_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_20_3 = cert44_layer_0_20_3 := by
  decide

theorem cert44_component_0_20_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_0_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 27 cert44_seen_0_20_0 = cert44_component_0_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_20_0 cert44_layer_0_20_0 26 cert44_layer_0_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 26 cert44_seen_0_20_1 = cert44_component_0_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_20_1 cert44_layer_0_20_1 25 cert44_layer_0_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 25 cert44_seen_0_20_2 = cert44_component_0_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_20_2 cert44_layer_0_20_2 24 cert44_layer_0_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 24 cert44_seen_0_20_3 = cert44_component_0_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_20_3 cert44_layer_0_20_3_eq 24

theorem cert44_step_0_20 :
    closedCollarIndexStepBool word fiber44 0 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_20)
    (by decide) (by decide)
    (by simpa [cert44_move_0_20] using cert44_component_0_20_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_24 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_0_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_0_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_0_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_24_0 = cert44_layer_0_24_0 := by
  decide

def cert44_seen_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_0_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_0_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_24_1 = cert44_layer_0_24_1 := by
  decide

def cert44_seen_0_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_0_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_0_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_24_2 = cert44_layer_0_24_2 := by
  decide

def cert44_seen_0_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_0_24_3 : List ChainEdge :=
  []

theorem cert44_layer_0_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_24_3 = cert44_layer_0_24_3 := by
  decide

theorem cert44_component_0_24_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_0_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 27 cert44_seen_0_24_0 = cert44_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_24_0 cert44_layer_0_24_0 26 cert44_layer_0_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 26 cert44_seen_0_24_1 = cert44_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_24_1 cert44_layer_0_24_1 25 cert44_layer_0_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 25 cert44_seen_0_24_2 = cert44_component_0_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_24_2 cert44_layer_0_24_2 24 cert44_layer_0_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 24 cert44_seen_0_24_3 = cert44_component_0_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_24_3 cert44_layer_0_24_3_eq 24

theorem cert44_step_0_24 :
    closedCollarIndexStepBool word fiber44 0 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_24)
    (by decide) (by decide)
    (by simpa [cert44_move_0_24] using cert44_component_0_24_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 1, edge := TauEdge.B5 } }

def cert44_component_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

def cert44_layer_1_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_1_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_0_0 = cert44_layer_1_0_0 := by
  decide

def cert44_seen_1_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_1_0_1 : List ChainEdge :=
  []

theorem cert44_layer_1_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_0_1 = cert44_layer_1_0_1 := by
  decide

theorem cert44_component_1_0_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = cert44_component_1_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 1, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 27 cert44_seen_1_0_0 = cert44_component_1_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_0_0 cert44_layer_1_0_0 26 cert44_layer_1_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 26 cert44_seen_1_0_1 = cert44_component_1_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_0_1 cert44_layer_1_0_1_eq 26

theorem cert44_step_1_0 :
    closedCollarIndexStepBool word fiber44 1 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_0)
    (by decide) (by decide)
    (by simpa [cert44_move_1_0] using cert44_component_1_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert44_component_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_seen_1_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_1_2_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_1_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_2_0 = cert44_layer_1_2_0 := by
  decide

def cert44_seen_1_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_1_2_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_1_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_2_1 = cert44_layer_1_2_1 := by
  decide

def cert44_seen_1_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_1_2_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_1_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_2_2 = cert44_layer_1_2_2 := by
  decide

def cert44_seen_1_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_1_2_3 : List ChainEdge :=
  []

theorem cert44_layer_1_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_2_3 = cert44_layer_1_2_3 := by
  decide

theorem cert44_component_1_2_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert44_component_1_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 27 cert44_seen_1_2_0 = cert44_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_2_0 cert44_layer_1_2_0 26 cert44_layer_1_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 26 cert44_seen_1_2_1 = cert44_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_2_1 cert44_layer_1_2_1 25 cert44_layer_1_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 25 cert44_seen_1_2_2 = cert44_component_1_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_2_2 cert44_layer_1_2_2 24 cert44_layer_1_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 24 cert44_seen_1_2_3 = cert44_component_1_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_2_3 cert44_layer_1_2_3_eq 24

theorem cert44_step_1_2 :
    closedCollarIndexStepBool word fiber44 1 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_2)
    (by decide) (by decide)
    (by simpa [cert44_move_1_2] using cert44_component_1_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert44_component_1_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_1_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_1_5_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_1_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_5_0 = cert44_layer_1_5_0 := by
  decide

def cert44_seen_1_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_1_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_1_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_5_1 = cert44_layer_1_5_1 := by
  decide

def cert44_seen_1_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_1_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_1_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_5_2 = cert44_layer_1_5_2 := by
  decide

def cert44_seen_1_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_1_5_3 : List ChainEdge :=
  []

theorem cert44_layer_1_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_5_3 = cert44_layer_1_5_3 := by
  decide

theorem cert44_component_1_5_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert44_component_1_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 27 cert44_seen_1_5_0 = cert44_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_5_0 cert44_layer_1_5_0 26 cert44_layer_1_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 26 cert44_seen_1_5_1 = cert44_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_5_1 cert44_layer_1_5_1 25 cert44_layer_1_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 25 cert44_seen_1_5_2 = cert44_component_1_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_5_2 cert44_layer_1_5_2 24 cert44_layer_1_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 24 cert44_seen_1_5_3 = cert44_component_1_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_5_3 cert44_layer_1_5_3_eq 24

theorem cert44_step_1_5 :
    closedCollarIndexStepBool word fiber44 1 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_5)
    (by decide) (by decide)
    (by simpa [cert44_move_1_5] using cert44_component_1_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_7 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_7_0 = cert44_layer_1_7_0 := by
  decide

def cert44_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_1_7_1 : List ChainEdge :=
  []

theorem cert44_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_7_1 = cert44_layer_1_7_1 := by
  decide

theorem cert44_component_1_7_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 27 cert44_seen_1_7_0 = cert44_component_1_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_7_0 cert44_layer_1_7_0 26 cert44_layer_1_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p 26 cert44_seen_1_7_1 = cert44_component_1_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.b LColor.p
    cert44_seen_1_7_1 cert44_layer_1_7_1_eq 26

theorem cert44_step_1_7 :
    closedCollarIndexStepBool word fiber44 1 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_7)
    (by decide) (by decide)
    (by simpa [cert44_move_1_7] using cert44_component_1_7_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_21 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_1_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_1_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_1_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_1_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_21_0 = cert44_layer_1_21_0 := by
  decide

def cert44_seen_1_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_1_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_1_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_21_1 = cert44_layer_1_21_1 := by
  decide

def cert44_seen_1_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_1_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_1_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_21_2 = cert44_layer_1_21_2 := by
  decide

def cert44_seen_1_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_1_21_3 : List ChainEdge :=
  []

theorem cert44_layer_1_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_21_3 = cert44_layer_1_21_3 := by
  decide

theorem cert44_component_1_21_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_1_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 27 cert44_seen_1_21_0 = cert44_component_1_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_21_0 cert44_layer_1_21_0 26 cert44_layer_1_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 26 cert44_seen_1_21_1 = cert44_component_1_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_21_1 cert44_layer_1_21_1 25 cert44_layer_1_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 25 cert44_seen_1_21_2 = cert44_component_1_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_21_2 cert44_layer_1_21_2 24 cert44_layer_1_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 24 cert44_seen_1_21_3 = cert44_component_1_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_21_3 cert44_layer_1_21_3_eq 24

theorem cert44_step_1_21 :
    closedCollarIndexStepBool word fiber44 1 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_21)
    (by decide) (by decide)
    (by simpa [cert44_move_1_21] using cert44_component_1_21_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_25 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_1_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_1_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_1_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_25_0 = cert44_layer_1_25_0 := by
  decide

def cert44_seen_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_1_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_1_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_25_1 = cert44_layer_1_25_1 := by
  decide

def cert44_seen_1_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_1_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_1_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_25_2 = cert44_layer_1_25_2 := by
  decide

def cert44_seen_1_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_1_25_3 : List ChainEdge :=
  []

theorem cert44_layer_1_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_25_3 = cert44_layer_1_25_3 := by
  decide

theorem cert44_component_1_25_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_1_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 27 cert44_seen_1_25_0 = cert44_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_25_0 cert44_layer_1_25_0 26 cert44_layer_1_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 26 cert44_seen_1_25_1 = cert44_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_25_1 cert44_layer_1_25_1 25 cert44_layer_1_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 25 cert44_seen_1_25_2 = cert44_component_1_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_25_2 cert44_layer_1_25_2 24 cert44_layer_1_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 24 cert44_seen_1_25_3 = cert44_component_1_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_25_3 cert44_layer_1_25_3_eq 24

theorem cert44_step_1_25 :
    closedCollarIndexStepBool word fiber44 1 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_25)
    (by decide) (by decide)
    (by simpa [cert44_move_1_25] using cert44_component_1_25_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert44_component_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_seen_2_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_2_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_2_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_1_0 = cert44_layer_2_1_0 := by
  decide

def cert44_seen_2_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_2_1_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_2_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_1_1 = cert44_layer_2_1_1 := by
  decide

def cert44_seen_2_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_2_1_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_2_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_1_2 = cert44_layer_2_1_2 := by
  decide

def cert44_seen_2_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_2_1_3 : List ChainEdge :=
  []

theorem cert44_layer_2_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_1_3 = cert44_layer_2_1_3 := by
  decide

theorem cert44_component_2_1_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert44_component_2_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 27 cert44_seen_2_1_0 = cert44_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_1_0 cert44_layer_2_1_0 26 cert44_layer_2_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 26 cert44_seen_2_1_1 = cert44_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_1_1 cert44_layer_2_1_1 25 cert44_layer_2_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 25 cert44_seen_2_1_2 = cert44_component_2_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_1_2 cert44_layer_2_1_2 24 cert44_layer_2_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 24 cert44_seen_2_1_3 = cert44_component_2_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_1_3 cert44_layer_2_1_3_eq 24

theorem cert44_step_2_1 :
    closedCollarIndexStepBool word fiber44 2 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_1)
    (by decide) (by decide)
    (by simpa [cert44_move_2_1] using cert44_component_2_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_8 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.b LColor.p cert44_seen_2_8_0 = cert44_layer_2_8_0 := by
  decide

def cert44_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_2_8_1 : List ChainEdge :=
  []

theorem cert44_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.b LColor.p cert44_seen_2_8_1 = cert44_layer_2_8_1 := by
  decide

theorem cert44_component_2_8_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.b LColor.p 27 cert44_seen_2_8_0 = cert44_component_2_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.b LColor.p
    cert44_seen_2_8_0 cert44_layer_2_8_0 26 cert44_layer_2_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.b LColor.p 26 cert44_seen_2_8_1 = cert44_component_2_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.b LColor.p
    cert44_seen_2_8_1 cert44_layer_2_8_1_eq 26

theorem cert44_step_2_8 :
    closedCollarIndexStepBool word fiber44 2 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_8)
    (by decide) (by decide)
    (by simpa [cert44_move_2_8] using cert44_component_2_8_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_22 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_2_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_2_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_2_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_2_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_22_0 = cert44_layer_2_22_0 := by
  decide

def cert44_seen_2_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_2_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_2_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_22_1 = cert44_layer_2_22_1 := by
  decide

def cert44_seen_2_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_2_22_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_2_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_22_2 = cert44_layer_2_22_2 := by
  decide

def cert44_seen_2_22_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_2_22_3 : List ChainEdge :=
  []

theorem cert44_layer_2_22_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_22_3 = cert44_layer_2_22_3 := by
  decide

theorem cert44_component_2_22_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_2_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 27 cert44_seen_2_22_0 = cert44_component_2_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_22_0 cert44_layer_2_22_0 26 cert44_layer_2_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 26 cert44_seen_2_22_1 = cert44_component_2_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_22_1 cert44_layer_2_22_1 25 cert44_layer_2_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 25 cert44_seen_2_22_2 = cert44_component_2_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_22_2 cert44_layer_2_22_2 24 cert44_layer_2_22_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 24 cert44_seen_2_22_3 = cert44_component_2_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_22_3 cert44_layer_2_22_3_eq 24

theorem cert44_step_2_22 :
    closedCollarIndexStepBool word fiber44 2 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_22)
    (by decide) (by decide)
    (by simpa [cert44_move_2_22] using cert44_component_2_22_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_26 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_2_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_2_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_2_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_26_0 = cert44_layer_2_26_0 := by
  decide

def cert44_seen_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_2_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_2_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_26_1 = cert44_layer_2_26_1 := by
  decide

def cert44_seen_2_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_2_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_2_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_26_2 = cert44_layer_2_26_2 := by
  decide

def cert44_seen_2_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_2_26_3 : List ChainEdge :=
  []

theorem cert44_layer_2_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_26_3 = cert44_layer_2_26_3 := by
  decide

theorem cert44_component_2_26_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_2_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 27 cert44_seen_2_26_0 = cert44_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_26_0 cert44_layer_2_26_0 26 cert44_layer_2_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 26 cert44_seen_2_26_1 = cert44_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_26_1 cert44_layer_2_26_1 25 cert44_layer_2_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 25 cert44_seen_2_26_2 = cert44_component_2_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_26_2 cert44_layer_2_26_2 24 cert44_layer_2_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 24 cert44_seen_2_26_3 = cert44_component_2_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_26_3 cert44_layer_2_26_3_eq 24

theorem cert44_step_2_26 :
    closedCollarIndexStepBool word fiber44 2 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_26)
    (by decide) (by decide)
    (by simpa [cert44_move_2_26] using cert44_component_2_26_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 1, edge := TauEdge.F4F5 } }

def cert44_component_3_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_seen_3_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_3_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_3_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_0_0 = cert44_layer_3_0_0 := by
  decide

def cert44_seen_3_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_3_0_1 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_3_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_0_1 = cert44_layer_3_0_1 := by
  decide

def cert44_seen_3_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_3_0_2 : List ChainEdge :=
  [{ occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_3_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_0_2 = cert44_layer_3_0_2 := by
  decide

def cert44_seen_3_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.B7 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_3_0_3 : List ChainEdge :=
  []

theorem cert44_layer_3_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_0_3 = cert44_layer_3_0_3 := by
  decide

theorem cert44_component_3_0_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = cert44_component_3_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 1, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 27 cert44_seen_3_0_0 = cert44_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_0_0 cert44_layer_3_0_0 26 cert44_layer_3_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 26 cert44_seen_3_0_1 = cert44_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_0_1 cert44_layer_3_0_1 25 cert44_layer_3_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 25 cert44_seen_3_0_2 = cert44_component_3_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_0_2 cert44_layer_3_0_2 24 cert44_layer_3_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 24 cert44_seen_3_0_3 = cert44_component_3_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_0_3 cert44_layer_3_0_3_eq 24

theorem cert44_step_3_0 :
    closedCollarIndexStepBool word fiber44 3 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_0)
    (by decide) (by decide)
    (by simpa [cert44_move_3_0] using cert44_component_3_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_9 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.b LColor.p cert44_seen_3_9_0 = cert44_layer_3_9_0 := by
  decide

def cert44_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_3_9_1 : List ChainEdge :=
  []

theorem cert44_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.b LColor.p cert44_seen_3_9_1 = cert44_layer_3_9_1 := by
  decide

theorem cert44_component_3_9_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.b LColor.p 27 cert44_seen_3_9_0 = cert44_component_3_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.b LColor.p
    cert44_seen_3_9_0 cert44_layer_3_9_0 26 cert44_layer_3_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.b LColor.p 26 cert44_seen_3_9_1 = cert44_component_3_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.b LColor.p
    cert44_seen_3_9_1 cert44_layer_3_9_1_eq 26

theorem cert44_step_3_9 :
    closedCollarIndexStepBool word fiber44 3 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_9)
    (by decide) (by decide)
    (by simpa [cert44_move_3_9] using cert44_component_3_9_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_23 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_3_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_3_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_3_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_3_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_23_0 = cert44_layer_3_23_0 := by
  decide

def cert44_seen_3_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_3_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_3_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_23_1 = cert44_layer_3_23_1 := by
  decide

def cert44_seen_3_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_3_23_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_3_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_23_2 = cert44_layer_3_23_2 := by
  decide

def cert44_seen_3_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_3_23_3 : List ChainEdge :=
  []

theorem cert44_layer_3_23_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_23_3 = cert44_layer_3_23_3 := by
  decide

theorem cert44_component_3_23_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_3_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 27 cert44_seen_3_23_0 = cert44_component_3_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_23_0 cert44_layer_3_23_0 26 cert44_layer_3_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 26 cert44_seen_3_23_1 = cert44_component_3_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_23_1 cert44_layer_3_23_1 25 cert44_layer_3_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 25 cert44_seen_3_23_2 = cert44_component_3_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_23_2 cert44_layer_3_23_2 24 cert44_layer_3_23_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 24 cert44_seen_3_23_3 = cert44_component_3_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_23_3 cert44_layer_3_23_3_eq 24

theorem cert44_step_3_23 :
    closedCollarIndexStepBool word fiber44 3 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_23)
    (by decide) (by decide)
    (by simpa [cert44_move_3_23] using cert44_component_3_23_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_27 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_3_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_3_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_3_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_27_0 = cert44_layer_3_27_0 := by
  decide

def cert44_seen_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_3_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_3_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_27_1 = cert44_layer_3_27_1 := by
  decide

def cert44_seen_3_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_3_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_3_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_27_2 = cert44_layer_3_27_2 := by
  decide

def cert44_seen_3_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_3_27_3 : List ChainEdge :=
  []

theorem cert44_layer_3_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_27_3 = cert44_layer_3_27_3 := by
  decide

theorem cert44_component_3_27_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_3_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 27 cert44_seen_3_27_0 = cert44_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_27_0 cert44_layer_3_27_0 26 cert44_layer_3_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 26 cert44_seen_3_27_1 = cert44_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_27_1 cert44_layer_3_27_1 25 cert44_layer_3_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 25 cert44_seen_3_27_2 = cert44_component_3_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_27_2 cert44_layer_3_27_2 24 cert44_layer_3_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 24 cert44_seen_3_27_3 = cert44_component_3_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_27_3 cert44_layer_3_27_3_eq 24

theorem cert44_step_3_27 :
    closedCollarIndexStepBool word fiber44 3 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_27)
    (by decide) (by decide)
    (by simpa [cert44_move_3_27] using cert44_component_3_27_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert44_component_4_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_seen_4_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_4_0_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_4_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_0_0 = cert44_layer_4_0_0 := by
  decide

def cert44_seen_4_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_4_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_4_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_0_1 = cert44_layer_4_0_1 := by
  decide

def cert44_seen_4_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_4_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_4_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_0_2 = cert44_layer_4_0_2 := by
  decide

def cert44_seen_4_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_4_0_3 : List ChainEdge :=
  []

theorem cert44_layer_4_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_0_3 = cert44_layer_4_0_3 := by
  decide

theorem cert44_component_4_0_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert44_component_4_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 27 cert44_seen_4_0_0 = cert44_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_0_0 cert44_layer_4_0_0 26 cert44_layer_4_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 26 cert44_seen_4_0_1 = cert44_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_0_1 cert44_layer_4_0_1 25 cert44_layer_4_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 25 cert44_seen_4_0_2 = cert44_component_4_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_0_2 cert44_layer_4_0_2 24 cert44_layer_4_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 24 cert44_seen_4_0_3 = cert44_component_4_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_0_3 cert44_layer_4_0_3_eq 24

theorem cert44_step_4_0 :
    closedCollarIndexStepBool word fiber44 4 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_0)
    (by decide) (by decide)
    (by simpa [cert44_move_4_0] using cert44_component_4_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_10 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.b LColor.p cert44_seen_4_10_0 = cert44_layer_4_10_0 := by
  decide

def cert44_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_4_10_1 : List ChainEdge :=
  []

theorem cert44_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.b LColor.p cert44_seen_4_10_1 = cert44_layer_4_10_1 := by
  decide

theorem cert44_component_4_10_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.b LColor.p 27 cert44_seen_4_10_0 = cert44_component_4_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.b LColor.p
    cert44_seen_4_10_0 cert44_layer_4_10_0 26 cert44_layer_4_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.b LColor.p 26 cert44_seen_4_10_1 = cert44_component_4_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.b LColor.p
    cert44_seen_4_10_1 cert44_layer_4_10_1_eq 26

theorem cert44_step_4_10 :
    closedCollarIndexStepBool word fiber44 4 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_10)
    (by decide) (by decide)
    (by simpa [cert44_move_4_10] using cert44_component_4_10_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_18 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_4_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_4_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_4_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_4_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_0 = cert44_layer_4_18_0 := by
  decide

def cert44_seen_4_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_4_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_4_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_1 = cert44_layer_4_18_1 := by
  decide

def cert44_seen_4_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_4_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_4_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_2 = cert44_layer_4_18_2 := by
  decide

def cert44_seen_4_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_4_18_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_4_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_3 = cert44_layer_4_18_3 := by
  decide

def cert44_seen_4_18_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_4_18_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_4_18_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_4 = cert44_layer_4_18_4 := by
  decide

def cert44_seen_4_18_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_4_18_5 : List ChainEdge :=
  []

theorem cert44_layer_4_18_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_18_5 = cert44_layer_4_18_5 := by
  decide

theorem cert44_component_4_18_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_4_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 27 cert44_seen_4_18_0 = cert44_component_4_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_0 cert44_layer_4_18_0 26 cert44_layer_4_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 26 cert44_seen_4_18_1 = cert44_component_4_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_1 cert44_layer_4_18_1 25 cert44_layer_4_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 25 cert44_seen_4_18_2 = cert44_component_4_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_2 cert44_layer_4_18_2 24 cert44_layer_4_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 24 cert44_seen_4_18_3 = cert44_component_4_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_3 cert44_layer_4_18_3 23 cert44_layer_4_18_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 23 cert44_seen_4_18_4 = cert44_component_4_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_4 cert44_layer_4_18_4 22 cert44_layer_4_18_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 22 cert44_seen_4_18_5 = cert44_component_4_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_18_5 cert44_layer_4_18_5_eq 22

theorem cert44_step_4_18 :
    closedCollarIndexStepBool word fiber44 4 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_18)
    (by decide) (by decide)
    (by simpa [cert44_move_4_18] using cert44_component_4_18_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_28 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_4_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_4_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_4_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_4_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_28_0 = cert44_layer_4_28_0 := by
  decide

def cert44_seen_4_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_4_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_4_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_28_1 = cert44_layer_4_28_1 := by
  decide

def cert44_seen_4_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_4_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_4_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_28_2 = cert44_layer_4_28_2 := by
  decide

def cert44_seen_4_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_4_28_3 : List ChainEdge :=
  []

theorem cert44_layer_4_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_28_3 = cert44_layer_4_28_3 := by
  decide

theorem cert44_component_4_28_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_4_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 27 cert44_seen_4_28_0 = cert44_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_28_0 cert44_layer_4_28_0 26 cert44_layer_4_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 26 cert44_seen_4_28_1 = cert44_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_28_1 cert44_layer_4_28_1 25 cert44_layer_4_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 25 cert44_seen_4_28_2 = cert44_component_4_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_28_2 cert44_layer_4_28_2 24 cert44_layer_4_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 24 cert44_seen_4_28_3 = cert44_component_4_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_28_3 cert44_layer_4_28_3_eq 24

theorem cert44_step_4_28 :
    closedCollarIndexStepBool word fiber44 4 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_28)
    (by decide) (by decide)
    (by simpa [cert44_move_4_28] using cert44_component_4_28_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 1, edge := TauEdge.F2F3 } }

def cert44_component_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_5_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_5_1_0 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_5_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_1_0 = cert44_layer_5_1_0 := by
  decide

def cert44_seen_5_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_5_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_5_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_1_1 = cert44_layer_5_1_1 := by
  decide

def cert44_seen_5_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_5_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_5_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_1_2 = cert44_layer_5_1_2 := by
  decide

def cert44_seen_5_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_5_1_3 : List ChainEdge :=
  []

theorem cert44_layer_5_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_1_3 = cert44_layer_5_1_3 := by
  decide

theorem cert44_component_5_1_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = cert44_component_5_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 1, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 27 cert44_seen_5_1_0 = cert44_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_1_0 cert44_layer_5_1_0 26 cert44_layer_5_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 26 cert44_seen_5_1_1 = cert44_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_1_1 cert44_layer_5_1_1 25 cert44_layer_5_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 25 cert44_seen_5_1_2 = cert44_component_5_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_1_2 cert44_layer_5_1_2 24 cert44_layer_5_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 24 cert44_seen_5_1_3 = cert44_component_5_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_1_3 cert44_layer_5_1_3_eq 24

theorem cert44_step_5_1 :
    closedCollarIndexStepBool word fiber44 5 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_1)
    (by decide) (by decide)
    (by simpa [cert44_move_5_1] using cert44_component_5_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_11 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.b LColor.p cert44_seen_5_11_0 = cert44_layer_5_11_0 := by
  decide

def cert44_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_5_11_1 : List ChainEdge :=
  []

theorem cert44_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.b LColor.p cert44_seen_5_11_1 = cert44_layer_5_11_1 := by
  decide

theorem cert44_component_5_11_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.b LColor.p 27 cert44_seen_5_11_0 = cert44_component_5_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.b LColor.p
    cert44_seen_5_11_0 cert44_layer_5_11_0 26 cert44_layer_5_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.b LColor.p 26 cert44_seen_5_11_1 = cert44_component_5_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.b LColor.p
    cert44_seen_5_11_1 cert44_layer_5_11_1_eq 26

theorem cert44_step_5_11 :
    closedCollarIndexStepBool word fiber44 5 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_11)
    (by decide) (by decide)
    (by simpa [cert44_move_5_11] using cert44_component_5_11_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_19 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_5_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_5_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_5_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_5_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_0 = cert44_layer_5_19_0 := by
  decide

def cert44_seen_5_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_5_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_5_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_1 = cert44_layer_5_19_1 := by
  decide

def cert44_seen_5_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_5_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_5_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_2 = cert44_layer_5_19_2 := by
  decide

def cert44_seen_5_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_5_19_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_5_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_3 = cert44_layer_5_19_3 := by
  decide

def cert44_seen_5_19_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_5_19_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_5_19_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_4 = cert44_layer_5_19_4 := by
  decide

def cert44_seen_5_19_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_5_19_5 : List ChainEdge :=
  []

theorem cert44_layer_5_19_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_19_5 = cert44_layer_5_19_5 := by
  decide

theorem cert44_component_5_19_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_5_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 27 cert44_seen_5_19_0 = cert44_component_5_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_0 cert44_layer_5_19_0 26 cert44_layer_5_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 26 cert44_seen_5_19_1 = cert44_component_5_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_1 cert44_layer_5_19_1 25 cert44_layer_5_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 25 cert44_seen_5_19_2 = cert44_component_5_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_2 cert44_layer_5_19_2 24 cert44_layer_5_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 24 cert44_seen_5_19_3 = cert44_component_5_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_3 cert44_layer_5_19_3 23 cert44_layer_5_19_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 23 cert44_seen_5_19_4 = cert44_component_5_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_4 cert44_layer_5_19_4 22 cert44_layer_5_19_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 22 cert44_seen_5_19_5 = cert44_component_5_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_19_5 cert44_layer_5_19_5_eq 22

theorem cert44_step_5_19 :
    closedCollarIndexStepBool word fiber44 5 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_19)
    (by decide) (by decide)
    (by simpa [cert44_move_5_19] using cert44_component_5_19_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_29 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_5_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_5_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_5_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_5_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_29_0 = cert44_layer_5_29_0 := by
  decide

def cert44_seen_5_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_5_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_5_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_29_1 = cert44_layer_5_29_1 := by
  decide

def cert44_seen_5_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_5_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_5_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_29_2 = cert44_layer_5_29_2 := by
  decide

def cert44_seen_5_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_5_29_3 : List ChainEdge :=
  []

theorem cert44_layer_5_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_29_3 = cert44_layer_5_29_3 := by
  decide

theorem cert44_component_5_29_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_5_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 27 cert44_seen_5_29_0 = cert44_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_29_0 cert44_layer_5_29_0 26 cert44_layer_5_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 26 cert44_seen_5_29_1 = cert44_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_29_1 cert44_layer_5_29_1 25 cert44_layer_5_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 25 cert44_seen_5_29_2 = cert44_component_5_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_29_2 cert44_layer_5_29_2 24 cert44_layer_5_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 24 cert44_seen_5_29_3 = cert44_component_5_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_29_3 cert44_layer_5_29_3_eq 24

theorem cert44_step_5_29 :
    closedCollarIndexStepBool word fiber44 5 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_29)
    (by decide) (by decide)
    (by simpa [cert44_move_5_29] using cert44_component_5_29_eq)
    (by decide) (by decide) (by decide)

def cert44_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.b LColor.p cert44_seen_6_0_0 = cert44_layer_6_0_0 := by
  decide

def cert44_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_6_0_1 : List ChainEdge :=
  []

theorem cert44_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.b LColor.p cert44_seen_6_0_1 = cert44_layer_6_0_1 := by
  decide

theorem cert44_component_6_0_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.b LColor.p 27 cert44_seen_6_0_0 = cert44_component_6_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.b LColor.p
    cert44_seen_6_0_0 cert44_layer_6_0_0 26 cert44_layer_6_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.b LColor.p 26 cert44_seen_6_0_1 = cert44_component_6_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 6 []) LColor.b LColor.p
    cert44_seen_6_0_1 cert44_layer_6_0_1_eq 26

theorem cert44_step_6_0 :
    closedCollarIndexStepBool word fiber44 6 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_6_0)
    (by decide) (by decide)
    (by simpa [cert44_move_6_0] using cert44_component_6_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_6_14 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_6_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_6_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_6_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_14_0 = cert44_layer_6_14_0 := by
  decide

def cert44_seen_6_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_6_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_6_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_14_1 = cert44_layer_6_14_1 := by
  decide

def cert44_seen_6_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_6_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_6_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_14_2 = cert44_layer_6_14_2 := by
  decide

def cert44_seen_6_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_6_14_3 : List ChainEdge :=
  []

theorem cert44_layer_6_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_14_3 = cert44_layer_6_14_3 := by
  decide

theorem cert44_component_6_14_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_6_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 27 cert44_seen_6_14_0 = cert44_component_6_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_14_0 cert44_layer_6_14_0 26 cert44_layer_6_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 26 cert44_seen_6_14_1 = cert44_component_6_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_14_1 cert44_layer_6_14_1 25 cert44_layer_6_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 25 cert44_seen_6_14_2 = cert44_component_6_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_14_2 cert44_layer_6_14_2 24 cert44_layer_6_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 24 cert44_seen_6_14_3 = cert44_component_6_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_14_3 cert44_layer_6_14_3_eq 24

theorem cert44_step_6_14 :
    closedCollarIndexStepBool word fiber44 6 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_6_14)
    (by decide) (by decide)
    (by simpa [cert44_move_6_14] using cert44_component_6_14_eq)
    (by decide) (by decide) (by decide)

def cert44_move_6_30 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_6_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_6_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_6_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_30_0 = cert44_layer_6_30_0 := by
  decide

def cert44_seen_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_6_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_6_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_30_1 = cert44_layer_6_30_1 := by
  decide

def cert44_seen_6_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_6_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_6_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_30_2 = cert44_layer_6_30_2 := by
  decide

def cert44_seen_6_30_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_6_30_3 : List ChainEdge :=
  []

theorem cert44_layer_6_30_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_30_3 = cert44_layer_6_30_3 := by
  decide

theorem cert44_component_6_30_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_6_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 27 cert44_seen_6_30_0 = cert44_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_30_0 cert44_layer_6_30_0 26 cert44_layer_6_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 26 cert44_seen_6_30_1 = cert44_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_30_1 cert44_layer_6_30_1 25 cert44_layer_6_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 25 cert44_seen_6_30_2 = cert44_component_6_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_30_2 cert44_layer_6_30_2 24 cert44_layer_6_30_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 24 cert44_seen_6_30_3 = cert44_component_6_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_30_3 cert44_layer_6_30_3_eq 24

theorem cert44_step_6_30 :
    closedCollarIndexStepBool word fiber44 6 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_6_30)
    (by decide) (by decide)
    (by simpa [cert44_move_6_30] using cert44_component_6_30_eq)
    (by decide) (by decide) (by decide)

def cert44_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.b LColor.p cert44_seen_7_1_0 = cert44_layer_7_1_0 := by
  decide

def cert44_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_7_1_1 : List ChainEdge :=
  []

theorem cert44_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.b LColor.p cert44_seen_7_1_1 = cert44_layer_7_1_1 := by
  decide

theorem cert44_component_7_1_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.b LColor.p 27 cert44_seen_7_1_0 = cert44_component_7_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.b LColor.p
    cert44_seen_7_1_0 cert44_layer_7_1_0 26 cert44_layer_7_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.b LColor.p 26 cert44_seen_7_1_1 = cert44_component_7_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 7 []) LColor.b LColor.p
    cert44_seen_7_1_1 cert44_layer_7_1_1_eq 26

theorem cert44_step_7_1 :
    closedCollarIndexStepBool word fiber44 7 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_7_1)
    (by decide) (by decide)
    (by simpa [cert44_move_7_1] using cert44_component_7_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_7_15 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_7_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_7_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_7_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_15_0 = cert44_layer_7_15_0 := by
  decide

def cert44_seen_7_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_7_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_7_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_15_1 = cert44_layer_7_15_1 := by
  decide

def cert44_seen_7_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_7_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_7_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_15_2 = cert44_layer_7_15_2 := by
  decide

def cert44_seen_7_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_7_15_3 : List ChainEdge :=
  []

theorem cert44_layer_7_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_15_3 = cert44_layer_7_15_3 := by
  decide

theorem cert44_component_7_15_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_7_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 27 cert44_seen_7_15_0 = cert44_component_7_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_15_0 cert44_layer_7_15_0 26 cert44_layer_7_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 26 cert44_seen_7_15_1 = cert44_component_7_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_15_1 cert44_layer_7_15_1 25 cert44_layer_7_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 25 cert44_seen_7_15_2 = cert44_component_7_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_15_2 cert44_layer_7_15_2 24 cert44_layer_7_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 24 cert44_seen_7_15_3 = cert44_component_7_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_15_3 cert44_layer_7_15_3_eq 24

theorem cert44_step_7_15 :
    closedCollarIndexStepBool word fiber44 7 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_7_15)
    (by decide) (by decide)
    (by simpa [cert44_move_7_15] using cert44_component_7_15_eq)
    (by decide) (by decide) (by decide)

def cert44_move_7_31 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_7_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_7_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_7_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_31_0 = cert44_layer_7_31_0 := by
  decide

def cert44_seen_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_7_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_7_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_31_1 = cert44_layer_7_31_1 := by
  decide

def cert44_seen_7_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_7_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_7_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_31_2 = cert44_layer_7_31_2 := by
  decide

def cert44_seen_7_31_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_7_31_3 : List ChainEdge :=
  []

theorem cert44_layer_7_31_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_31_3 = cert44_layer_7_31_3 := by
  decide

theorem cert44_component_7_31_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_7_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 27 cert44_seen_7_31_0 = cert44_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_31_0 cert44_layer_7_31_0 26 cert44_layer_7_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 26 cert44_seen_7_31_1 = cert44_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_31_1 cert44_layer_7_31_1 25 cert44_layer_7_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 25 cert44_seen_7_31_2 = cert44_component_7_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_31_2 cert44_layer_7_31_2 24 cert44_layer_7_31_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 24 cert44_seen_7_31_3 = cert44_component_7_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_31_3 cert44_layer_7_31_3_eq 24

theorem cert44_step_7_31 :
    closedCollarIndexStepBool word fiber44 7 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_7_31)
    (by decide) (by decide)
    (by simpa [cert44_move_7_31] using cert44_component_7_31_eq)
    (by decide) (by decide) (by decide)

def cert44_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.b LColor.p cert44_seen_8_2_0 = cert44_layer_8_2_0 := by
  decide

def cert44_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_8_2_1 : List ChainEdge :=
  []

theorem cert44_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.b LColor.p cert44_seen_8_2_1 = cert44_layer_8_2_1 := by
  decide

theorem cert44_component_8_2_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.b LColor.p 27 cert44_seen_8_2_0 = cert44_component_8_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.b LColor.p
    cert44_seen_8_2_0 cert44_layer_8_2_0 26 cert44_layer_8_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.b LColor.p 26 cert44_seen_8_2_1 = cert44_component_8_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 8 []) LColor.b LColor.p
    cert44_seen_8_2_1 cert44_layer_8_2_1_eq 26

theorem cert44_step_8_2 :
    closedCollarIndexStepBool word fiber44 8 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_8_2)
    (by decide) (by decide)
    (by simpa [cert44_move_8_2] using cert44_component_8_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_8_16 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_8_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_8_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_8_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_8_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_16_0 = cert44_layer_8_16_0 := by
  decide

def cert44_seen_8_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_8_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_8_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_16_1 = cert44_layer_8_16_1 := by
  decide

def cert44_seen_8_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_8_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_8_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_16_2 = cert44_layer_8_16_2 := by
  decide

def cert44_seen_8_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_8_16_3 : List ChainEdge :=
  []

theorem cert44_layer_8_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_16_3 = cert44_layer_8_16_3 := by
  decide

theorem cert44_component_8_16_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_8_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 27 cert44_seen_8_16_0 = cert44_component_8_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_16_0 cert44_layer_8_16_0 26 cert44_layer_8_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 26 cert44_seen_8_16_1 = cert44_component_8_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_16_1 cert44_layer_8_16_1 25 cert44_layer_8_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 25 cert44_seen_8_16_2 = cert44_component_8_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_16_2 cert44_layer_8_16_2 24 cert44_layer_8_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 24 cert44_seen_8_16_3 = cert44_component_8_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_16_3 cert44_layer_8_16_3_eq 24

theorem cert44_step_8_16 :
    closedCollarIndexStepBool word fiber44 8 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_8_16)
    (by decide) (by decide)
    (by simpa [cert44_move_8_16] using cert44_component_8_16_eq)
    (by decide) (by decide) (by decide)

def cert44_move_8_32 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_8_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_8_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_8_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_32_0 = cert44_layer_8_32_0 := by
  decide

def cert44_seen_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_8_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_8_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_32_1 = cert44_layer_8_32_1 := by
  decide

def cert44_seen_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_8_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_8_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_32_2 = cert44_layer_8_32_2 := by
  decide

def cert44_seen_8_32_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_8_32_3 : List ChainEdge :=
  []

theorem cert44_layer_8_32_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_32_3 = cert44_layer_8_32_3 := by
  decide

theorem cert44_component_8_32_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_8_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 27 cert44_seen_8_32_0 = cert44_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_32_0 cert44_layer_8_32_0 26 cert44_layer_8_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 26 cert44_seen_8_32_1 = cert44_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_32_1 cert44_layer_8_32_1 25 cert44_layer_8_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 25 cert44_seen_8_32_2 = cert44_component_8_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_32_2 cert44_layer_8_32_2 24 cert44_layer_8_32_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 24 cert44_seen_8_32_3 = cert44_component_8_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_32_3 cert44_layer_8_32_3_eq 24

theorem cert44_step_8_32 :
    closedCollarIndexStepBool word fiber44 8 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_8_32)
    (by decide) (by decide)
    (by simpa [cert44_move_8_32] using cert44_component_8_32_eq)
    (by decide) (by decide) (by decide)

def cert44_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.b LColor.p cert44_seen_9_3_0 = cert44_layer_9_3_0 := by
  decide

def cert44_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_9_3_1 : List ChainEdge :=
  []

theorem cert44_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.b LColor.p cert44_seen_9_3_1 = cert44_layer_9_3_1 := by
  decide

theorem cert44_component_9_3_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.b LColor.p 27 cert44_seen_9_3_0 = cert44_component_9_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.b LColor.p
    cert44_seen_9_3_0 cert44_layer_9_3_0 26 cert44_layer_9_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.b LColor.p 26 cert44_seen_9_3_1 = cert44_component_9_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 9 []) LColor.b LColor.p
    cert44_seen_9_3_1 cert44_layer_9_3_1_eq 26

theorem cert44_step_9_3 :
    closedCollarIndexStepBool word fiber44 9 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_9_3)
    (by decide) (by decide)
    (by simpa [cert44_move_9_3] using cert44_component_9_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_9_17 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_9_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_9_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_9_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_9_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_17_0 = cert44_layer_9_17_0 := by
  decide

def cert44_seen_9_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_9_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_9_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_17_1 = cert44_layer_9_17_1 := by
  decide

def cert44_seen_9_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_9_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_9_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_17_2 = cert44_layer_9_17_2 := by
  decide

def cert44_seen_9_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_9_17_3 : List ChainEdge :=
  []

theorem cert44_layer_9_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_17_3 = cert44_layer_9_17_3 := by
  decide

theorem cert44_component_9_17_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_9_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 27 cert44_seen_9_17_0 = cert44_component_9_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_17_0 cert44_layer_9_17_0 26 cert44_layer_9_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 26 cert44_seen_9_17_1 = cert44_component_9_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_17_1 cert44_layer_9_17_1 25 cert44_layer_9_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 25 cert44_seen_9_17_2 = cert44_component_9_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_17_2 cert44_layer_9_17_2 24 cert44_layer_9_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 24 cert44_seen_9_17_3 = cert44_component_9_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_17_3 cert44_layer_9_17_3_eq 24

theorem cert44_step_9_17 :
    closedCollarIndexStepBool word fiber44 9 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_9_17)
    (by decide) (by decide)
    (by simpa [cert44_move_9_17] using cert44_component_9_17_eq)
    (by decide) (by decide) (by decide)

def cert44_move_9_33 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_9_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_9_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_9_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_33_0 = cert44_layer_9_33_0 := by
  decide

def cert44_seen_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_9_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_9_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_33_1 = cert44_layer_9_33_1 := by
  decide

def cert44_seen_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_9_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_9_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_33_2 = cert44_layer_9_33_2 := by
  decide

def cert44_seen_9_33_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_9_33_3 : List ChainEdge :=
  []

theorem cert44_layer_9_33_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_33_3 = cert44_layer_9_33_3 := by
  decide

theorem cert44_component_9_33_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_9_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 27 cert44_seen_9_33_0 = cert44_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_33_0 cert44_layer_9_33_0 26 cert44_layer_9_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 26 cert44_seen_9_33_1 = cert44_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_33_1 cert44_layer_9_33_1 25 cert44_layer_9_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 25 cert44_seen_9_33_2 = cert44_component_9_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_33_2 cert44_layer_9_33_2 24 cert44_layer_9_33_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 24 cert44_seen_9_33_3 = cert44_component_9_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_33_3 cert44_layer_9_33_3_eq 24

theorem cert44_step_9_33 :
    closedCollarIndexStepBool word fiber44 9 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_9_33)
    (by decide) (by decide)
    (by simpa [cert44_move_9_33] using cert44_component_9_33_eq)
    (by decide) (by decide) (by decide)

def cert44_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.b LColor.p cert44_seen_10_4_0 = cert44_layer_10_4_0 := by
  decide

def cert44_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_10_4_1 : List ChainEdge :=
  []

theorem cert44_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.b LColor.p cert44_seen_10_4_1 = cert44_layer_10_4_1 := by
  decide

theorem cert44_component_10_4_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.b LColor.p 27 cert44_seen_10_4_0 = cert44_component_10_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.b LColor.p
    cert44_seen_10_4_0 cert44_layer_10_4_0 26 cert44_layer_10_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.b LColor.p 26 cert44_seen_10_4_1 = cert44_component_10_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 10 []) LColor.b LColor.p
    cert44_seen_10_4_1 cert44_layer_10_4_1_eq 26

theorem cert44_step_10_4 :
    closedCollarIndexStepBool word fiber44 10 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_10_4)
    (by decide) (by decide)
    (by simpa [cert44_move_10_4] using cert44_component_10_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_10_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_10_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_10_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_10_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_10_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_0 = cert44_layer_10_12_0 := by
  decide

def cert44_seen_10_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_10_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_10_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_1 = cert44_layer_10_12_1 := by
  decide

def cert44_seen_10_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_10_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_10_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_2 = cert44_layer_10_12_2 := by
  decide

def cert44_seen_10_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_10_12_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_10_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_3 = cert44_layer_10_12_3 := by
  decide

def cert44_seen_10_12_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_10_12_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_10_12_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_4 = cert44_layer_10_12_4 := by
  decide

def cert44_seen_10_12_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_10_12_5 : List ChainEdge :=
  []

theorem cert44_layer_10_12_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_12_5 = cert44_layer_10_12_5 := by
  decide

theorem cert44_component_10_12_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_10_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 27 cert44_seen_10_12_0 = cert44_component_10_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_0 cert44_layer_10_12_0 26 cert44_layer_10_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 26 cert44_seen_10_12_1 = cert44_component_10_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_1 cert44_layer_10_12_1 25 cert44_layer_10_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 25 cert44_seen_10_12_2 = cert44_component_10_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_2 cert44_layer_10_12_2 24 cert44_layer_10_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 24 cert44_seen_10_12_3 = cert44_component_10_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_3 cert44_layer_10_12_3 23 cert44_layer_10_12_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 23 cert44_seen_10_12_4 = cert44_component_10_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_4 cert44_layer_10_12_4 22 cert44_layer_10_12_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 22 cert44_seen_10_12_5 = cert44_component_10_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_12_5 cert44_layer_10_12_5_eq 22

theorem cert44_step_10_12 :
    closedCollarIndexStepBool word fiber44 10 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_10_12)
    (by decide) (by decide)
    (by simpa [cert44_move_10_12] using cert44_component_10_12_eq)
    (by decide) (by decide) (by decide)

def cert44_move_10_34 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_10_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_10_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_10_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_34_0 = cert44_layer_10_34_0 := by
  decide

def cert44_seen_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_10_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_10_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_34_1 = cert44_layer_10_34_1 := by
  decide

def cert44_seen_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_10_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_10_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_34_2 = cert44_layer_10_34_2 := by
  decide

def cert44_seen_10_34_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_10_34_3 : List ChainEdge :=
  []

theorem cert44_layer_10_34_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_34_3 = cert44_layer_10_34_3 := by
  decide

theorem cert44_component_10_34_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_10_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 27 cert44_seen_10_34_0 = cert44_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_34_0 cert44_layer_10_34_0 26 cert44_layer_10_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 26 cert44_seen_10_34_1 = cert44_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_34_1 cert44_layer_10_34_1 25 cert44_layer_10_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 25 cert44_seen_10_34_2 = cert44_component_10_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_34_2 cert44_layer_10_34_2 24 cert44_layer_10_34_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 24 cert44_seen_10_34_3 = cert44_component_10_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_34_3 cert44_layer_10_34_3_eq 24

theorem cert44_step_10_34 :
    closedCollarIndexStepBool word fiber44 10 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_10_34)
    (by decide) (by decide)
    (by simpa [cert44_move_10_34] using cert44_component_10_34_eq)
    (by decide) (by decide) (by decide)

def cert44_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B5 } }

def cert44_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

def cert44_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.b LColor.p cert44_seen_11_5_0 = cert44_layer_11_5_0 := by
  decide

def cert44_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_11_5_1 : List ChainEdge :=
  []

theorem cert44_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.b LColor.p cert44_seen_11_5_1 = cert44_layer_11_5_1 := by
  decide

theorem cert44_component_11_5_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = cert44_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.b LColor.p 27 cert44_seen_11_5_0 = cert44_component_11_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.b LColor.p
    cert44_seen_11_5_0 cert44_layer_11_5_0 26 cert44_layer_11_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.b LColor.p 26 cert44_seen_11_5_1 = cert44_component_11_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 11 []) LColor.b LColor.p
    cert44_seen_11_5_1 cert44_layer_11_5_1_eq 26

theorem cert44_step_11_5 :
    closedCollarIndexStepBool word fiber44 11 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_11_5)
    (by decide) (by decide)
    (by simpa [cert44_move_11_5] using cert44_component_11_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_11_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_11_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_11_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_11_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_11_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_0 = cert44_layer_11_13_0 := by
  decide

def cert44_seen_11_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_11_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_11_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_1 = cert44_layer_11_13_1 := by
  decide

def cert44_seen_11_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_11_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_11_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_2 = cert44_layer_11_13_2 := by
  decide

def cert44_seen_11_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_11_13_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_11_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_3 = cert44_layer_11_13_3 := by
  decide

def cert44_seen_11_13_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_11_13_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_11_13_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_4 = cert44_layer_11_13_4 := by
  decide

def cert44_seen_11_13_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_11_13_5 : List ChainEdge :=
  []

theorem cert44_layer_11_13_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_13_5 = cert44_layer_11_13_5 := by
  decide

theorem cert44_component_11_13_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_11_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 27 cert44_seen_11_13_0 = cert44_component_11_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_0 cert44_layer_11_13_0 26 cert44_layer_11_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 26 cert44_seen_11_13_1 = cert44_component_11_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_1 cert44_layer_11_13_1 25 cert44_layer_11_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 25 cert44_seen_11_13_2 = cert44_component_11_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_2 cert44_layer_11_13_2 24 cert44_layer_11_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 24 cert44_seen_11_13_3 = cert44_component_11_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_3 cert44_layer_11_13_3 23 cert44_layer_11_13_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 23 cert44_seen_11_13_4 = cert44_component_11_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_4 cert44_layer_11_13_4 22 cert44_layer_11_13_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 22 cert44_seen_11_13_5 = cert44_component_11_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_13_5 cert44_layer_11_13_5_eq 22

theorem cert44_step_11_13 :
    closedCollarIndexStepBool word fiber44 11 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_11_13)
    (by decide) (by decide)
    (by simpa [cert44_move_11_13] using cert44_component_11_13_eq)
    (by decide) (by decide) (by decide)

def cert44_move_11_35 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_11_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_11_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_11_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_35_0 = cert44_layer_11_35_0 := by
  decide

def cert44_seen_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_11_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_11_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_35_1 = cert44_layer_11_35_1 := by
  decide

def cert44_seen_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_11_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_11_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_35_2 = cert44_layer_11_35_2 := by
  decide

def cert44_seen_11_35_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_11_35_3 : List ChainEdge :=
  []

theorem cert44_layer_11_35_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_35_3 = cert44_layer_11_35_3 := by
  decide

theorem cert44_component_11_35_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_11_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 27 cert44_seen_11_35_0 = cert44_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_35_0 cert44_layer_11_35_0 26 cert44_layer_11_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 26 cert44_seen_11_35_1 = cert44_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_35_1 cert44_layer_11_35_1 25 cert44_layer_11_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 25 cert44_seen_11_35_2 = cert44_component_11_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_35_2 cert44_layer_11_35_2 24 cert44_layer_11_35_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 24 cert44_seen_11_35_3 = cert44_component_11_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_35_3 cert44_layer_11_35_3_eq 24

theorem cert44_step_11_35 :
    closedCollarIndexStepBool word fiber44 11 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_11_35)
    (by decide) (by decide)
    (by simpa [cert44_move_11_35] using cert44_component_11_35_eq)
    (by decide) (by decide) (by decide)

def cert44_move_12_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_12_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_12_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_12_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_12_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_0 = cert44_layer_12_10_0 := by
  decide

def cert44_seen_12_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_12_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_12_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_1 = cert44_layer_12_10_1 := by
  decide

def cert44_seen_12_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_12_10_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_12_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_2 = cert44_layer_12_10_2 := by
  decide

def cert44_seen_12_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_12_10_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_12_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_3 = cert44_layer_12_10_3 := by
  decide

def cert44_seen_12_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_12_10_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_12_10_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_4 = cert44_layer_12_10_4 := by
  decide

def cert44_seen_12_10_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_12_10_5 : List ChainEdge :=
  []

theorem cert44_layer_12_10_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_10_5 = cert44_layer_12_10_5 := by
  decide

theorem cert44_component_12_10_eq :
    closedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_12_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 27 cert44_seen_12_10_0 = cert44_component_12_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_0 cert44_layer_12_10_0 26 cert44_layer_12_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 26 cert44_seen_12_10_1 = cert44_component_12_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_1 cert44_layer_12_10_1 25 cert44_layer_12_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 25 cert44_seen_12_10_2 = cert44_component_12_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_2 cert44_layer_12_10_2 24 cert44_layer_12_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 24 cert44_seen_12_10_3 = cert44_component_12_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_3 cert44_layer_12_10_3 23 cert44_layer_12_10_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 23 cert44_seen_12_10_4 = cert44_component_12_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_4 cert44_layer_12_10_4 22 cert44_layer_12_10_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 22 cert44_seen_12_10_5 = cert44_component_12_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_10_5 cert44_layer_12_10_5_eq 22

theorem cert44_step_12_10 :
    closedCollarIndexStepBool word fiber44 12 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_12_10)
    (by decide) (by decide)
    (by simpa [cert44_move_12_10] using cert44_component_12_10_eq)
    (by decide) (by decide) (by decide)

def cert44_move_13_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_13_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_13_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_13_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_13_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_0 = cert44_layer_13_11_0 := by
  decide

def cert44_seen_13_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_13_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_13_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_1 = cert44_layer_13_11_1 := by
  decide

def cert44_seen_13_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_13_11_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_13_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_2 = cert44_layer_13_11_2 := by
  decide

def cert44_seen_13_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_13_11_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_13_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_3 = cert44_layer_13_11_3 := by
  decide

def cert44_seen_13_11_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_13_11_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_13_11_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_4 = cert44_layer_13_11_4 := by
  decide

def cert44_seen_13_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_13_11_5 : List ChainEdge :=
  []

theorem cert44_layer_13_11_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_11_5 = cert44_layer_13_11_5 := by
  decide

theorem cert44_component_13_11_eq :
    closedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_13_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 27 cert44_seen_13_11_0 = cert44_component_13_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_0 cert44_layer_13_11_0 26 cert44_layer_13_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 26 cert44_seen_13_11_1 = cert44_component_13_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_1 cert44_layer_13_11_1 25 cert44_layer_13_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 25 cert44_seen_13_11_2 = cert44_component_13_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_2 cert44_layer_13_11_2 24 cert44_layer_13_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 24 cert44_seen_13_11_3 = cert44_component_13_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_3 cert44_layer_13_11_3 23 cert44_layer_13_11_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 23 cert44_seen_13_11_4 = cert44_component_13_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_4 cert44_layer_13_11_4 22 cert44_layer_13_11_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 22 cert44_seen_13_11_5 = cert44_component_13_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_11_5 cert44_layer_13_11_5_eq 22

theorem cert44_step_13_11 :
    closedCollarIndexStepBool word fiber44 13 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_13_11)
    (by decide) (by decide)
    (by simpa [cert44_move_13_11] using cert44_component_13_11_eq)
    (by decide) (by decide) (by decide)

def cert44_move_14_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_14_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_14_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_14_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_6_0 = cert44_layer_14_6_0 := by
  decide

def cert44_seen_14_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_14_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_14_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_6_1 = cert44_layer_14_6_1 := by
  decide

def cert44_seen_14_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_14_6_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_14_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_6_2 = cert44_layer_14_6_2 := by
  decide

def cert44_seen_14_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_14_6_3 : List ChainEdge :=
  []

theorem cert44_layer_14_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_6_3 = cert44_layer_14_6_3 := by
  decide

theorem cert44_component_14_6_eq :
    closedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_14_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 27 cert44_seen_14_6_0 = cert44_component_14_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_6_0 cert44_layer_14_6_0 26 cert44_layer_14_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 26 cert44_seen_14_6_1 = cert44_component_14_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_6_1 cert44_layer_14_6_1 25 cert44_layer_14_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 25 cert44_seen_14_6_2 = cert44_component_14_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_6_2 cert44_layer_14_6_2 24 cert44_layer_14_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 24 cert44_seen_14_6_3 = cert44_component_14_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_6_3 cert44_layer_14_6_3_eq 24

theorem cert44_step_14_6 :
    closedCollarIndexStepBool word fiber44 14 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_14_6)
    (by decide) (by decide)
    (by simpa [cert44_move_14_6] using cert44_component_14_6_eq)
    (by decide) (by decide) (by decide)

def cert44_move_15_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_15_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_15_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_15_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_7_0 = cert44_layer_15_7_0 := by
  decide

def cert44_seen_15_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_15_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_15_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_7_1 = cert44_layer_15_7_1 := by
  decide

def cert44_seen_15_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_15_7_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_15_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_7_2 = cert44_layer_15_7_2 := by
  decide

def cert44_seen_15_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_15_7_3 : List ChainEdge :=
  []

theorem cert44_layer_15_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_7_3 = cert44_layer_15_7_3 := by
  decide

theorem cert44_component_15_7_eq :
    closedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_15_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 27 cert44_seen_15_7_0 = cert44_component_15_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_7_0 cert44_layer_15_7_0 26 cert44_layer_15_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 26 cert44_seen_15_7_1 = cert44_component_15_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_7_1 cert44_layer_15_7_1 25 cert44_layer_15_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 25 cert44_seen_15_7_2 = cert44_component_15_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_7_2 cert44_layer_15_7_2 24 cert44_layer_15_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 24 cert44_seen_15_7_3 = cert44_component_15_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_7_3 cert44_layer_15_7_3_eq 24

theorem cert44_step_15_7 :
    closedCollarIndexStepBool word fiber44 15 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_15_7)
    (by decide) (by decide)
    (by simpa [cert44_move_15_7] using cert44_component_15_7_eq)
    (by decide) (by decide) (by decide)

def cert44_move_16_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_16_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_16_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_16_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_16_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_8_0 = cert44_layer_16_8_0 := by
  decide

def cert44_seen_16_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_16_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_16_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_8_1 = cert44_layer_16_8_1 := by
  decide

def cert44_seen_16_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_16_8_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_16_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_8_2 = cert44_layer_16_8_2 := by
  decide

def cert44_seen_16_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_16_8_3 : List ChainEdge :=
  []

theorem cert44_layer_16_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_8_3 = cert44_layer_16_8_3 := by
  decide

theorem cert44_component_16_8_eq :
    closedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_16_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 27 cert44_seen_16_8_0 = cert44_component_16_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_8_0 cert44_layer_16_8_0 26 cert44_layer_16_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 26 cert44_seen_16_8_1 = cert44_component_16_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_8_1 cert44_layer_16_8_1 25 cert44_layer_16_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 25 cert44_seen_16_8_2 = cert44_component_16_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_8_2 cert44_layer_16_8_2 24 cert44_layer_16_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 24 cert44_seen_16_8_3 = cert44_component_16_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_8_3 cert44_layer_16_8_3_eq 24

theorem cert44_step_16_8 :
    closedCollarIndexStepBool word fiber44 16 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_16_8)
    (by decide) (by decide)
    (by simpa [cert44_move_16_8] using cert44_component_16_8_eq)
    (by decide) (by decide) (by decide)

def cert44_move_17_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_17_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_17_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_17_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_17_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_9_0 = cert44_layer_17_9_0 := by
  decide

def cert44_seen_17_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_17_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_17_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_9_1 = cert44_layer_17_9_1 := by
  decide

def cert44_seen_17_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_17_9_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_17_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_9_2 = cert44_layer_17_9_2 := by
  decide

def cert44_seen_17_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_17_9_3 : List ChainEdge :=
  []

theorem cert44_layer_17_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_9_3 = cert44_layer_17_9_3 := by
  decide

theorem cert44_component_17_9_eq :
    closedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_17_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 27 cert44_seen_17_9_0 = cert44_component_17_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_9_0 cert44_layer_17_9_0 26 cert44_layer_17_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 26 cert44_seen_17_9_1 = cert44_component_17_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_9_1 cert44_layer_17_9_1 25 cert44_layer_17_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 25 cert44_seen_17_9_2 = cert44_component_17_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_9_2 cert44_layer_17_9_2 24 cert44_layer_17_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 24 cert44_seen_17_9_3 = cert44_component_17_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_9_3 cert44_layer_17_9_3_eq 24

theorem cert44_step_17_9 :
    closedCollarIndexStepBool word fiber44 17 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_17_9)
    (by decide) (by decide)
    (by simpa [cert44_move_17_9] using cert44_component_17_9_eq)
    (by decide) (by decide) (by decide)

def cert44_move_18_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_18_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_18_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_18_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_18_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_0 = cert44_layer_18_4_0 := by
  decide

def cert44_seen_18_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_18_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_18_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_1 = cert44_layer_18_4_1 := by
  decide

def cert44_seen_18_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_18_4_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_18_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_2 = cert44_layer_18_4_2 := by
  decide

def cert44_seen_18_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_18_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_18_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_3 = cert44_layer_18_4_3 := by
  decide

def cert44_seen_18_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_18_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_18_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_4 = cert44_layer_18_4_4 := by
  decide

def cert44_seen_18_4_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_18_4_5 : List ChainEdge :=
  []

theorem cert44_layer_18_4_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.p cert44_seen_18_4_5 = cert44_layer_18_4_5 := by
  decide

theorem cert44_component_18_4_eq :
    closedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_18_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 18 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 27 cert44_seen_18_4_0 = cert44_component_18_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_0 cert44_layer_18_4_0 26 cert44_layer_18_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 26 cert44_seen_18_4_1 = cert44_component_18_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_1 cert44_layer_18_4_1 25 cert44_layer_18_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 25 cert44_seen_18_4_2 = cert44_component_18_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_2 cert44_layer_18_4_2 24 cert44_layer_18_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 24 cert44_seen_18_4_3 = cert44_component_18_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_3 cert44_layer_18_4_3 23 cert44_layer_18_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 23 cert44_seen_18_4_4 = cert44_component_18_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_4 cert44_layer_18_4_4 22 cert44_layer_18_4_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.p 22 cert44_seen_18_4_5 = cert44_component_18_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 18 []) LColor.r LColor.p
    cert44_seen_18_4_5 cert44_layer_18_4_5_eq 22

theorem cert44_step_18_4 :
    closedCollarIndexStepBool word fiber44 18 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_18_4)
    (by decide) (by decide)
    (by simpa [cert44_move_18_4] using cert44_component_18_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_18_40 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_18_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_seen_18_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_18_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_18_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_40_0 = cert44_layer_18_40_0 := by
  decide

def cert44_seen_18_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_18_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_18_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_40_1 = cert44_layer_18_40_1 := by
  decide

def cert44_seen_18_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_18_40_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_18_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_40_2 = cert44_layer_18_40_2 := by
  decide

def cert44_seen_18_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_18_40_3 : List ChainEdge :=
  []

theorem cert44_layer_18_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_40_3 = cert44_layer_18_40_3 := by
  decide

theorem cert44_component_18_40_eq :
    closedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_18_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 27 cert44_seen_18_40_0 = cert44_component_18_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_40_0 cert44_layer_18_40_0 26 cert44_layer_18_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 26 cert44_seen_18_40_1 = cert44_component_18_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_40_1 cert44_layer_18_40_1 25 cert44_layer_18_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 25 cert44_seen_18_40_2 = cert44_component_18_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_40_2 cert44_layer_18_40_2 24 cert44_layer_18_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 24 cert44_seen_18_40_3 = cert44_component_18_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_40_3 cert44_layer_18_40_3_eq 24

theorem cert44_step_18_40 :
    closedCollarIndexStepBool word fiber44 18 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_18_40)
    (by decide) (by decide)
    (by simpa [cert44_move_18_40] using cert44_component_18_40_eq)
    (by decide) (by decide) (by decide)

def cert44_move_19_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_19_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_19_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_19_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_19_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_0 = cert44_layer_19_5_0 := by
  decide

def cert44_seen_19_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_19_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_19_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_1 = cert44_layer_19_5_1 := by
  decide

def cert44_seen_19_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_19_5_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_19_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_2 = cert44_layer_19_5_2 := by
  decide

def cert44_seen_19_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_19_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_19_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_3 = cert44_layer_19_5_3 := by
  decide

def cert44_seen_19_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_19_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_19_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_4 = cert44_layer_19_5_4 := by
  decide

def cert44_seen_19_5_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_19_5_5 : List ChainEdge :=
  []

theorem cert44_layer_19_5_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.p cert44_seen_19_5_5 = cert44_layer_19_5_5 := by
  decide

theorem cert44_component_19_5_eq :
    closedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_19_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 19 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 27 cert44_seen_19_5_0 = cert44_component_19_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_0 cert44_layer_19_5_0 26 cert44_layer_19_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 26 cert44_seen_19_5_1 = cert44_component_19_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_1 cert44_layer_19_5_1 25 cert44_layer_19_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 25 cert44_seen_19_5_2 = cert44_component_19_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_2 cert44_layer_19_5_2 24 cert44_layer_19_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 24 cert44_seen_19_5_3 = cert44_component_19_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_3 cert44_layer_19_5_3 23 cert44_layer_19_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 23 cert44_seen_19_5_4 = cert44_component_19_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_4 cert44_layer_19_5_4 22 cert44_layer_19_5_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.p 22 cert44_seen_19_5_5 = cert44_component_19_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 19 []) LColor.r LColor.p
    cert44_seen_19_5_5 cert44_layer_19_5_5_eq 22

theorem cert44_step_19_5 :
    closedCollarIndexStepBool word fiber44 19 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_19_5)
    (by decide) (by decide)
    (by simpa [cert44_move_19_5] using cert44_component_19_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_19_41 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_19_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_seen_19_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_19_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_19_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_41_0 = cert44_layer_19_41_0 := by
  decide

def cert44_seen_19_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_19_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_19_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_41_1 = cert44_layer_19_41_1 := by
  decide

def cert44_seen_19_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_19_41_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_19_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_41_2 = cert44_layer_19_41_2 := by
  decide

def cert44_seen_19_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_19_41_3 : List ChainEdge :=
  []

theorem cert44_layer_19_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_41_3 = cert44_layer_19_41_3 := by
  decide

theorem cert44_component_19_41_eq :
    closedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_19_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 27 cert44_seen_19_41_0 = cert44_component_19_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_41_0 cert44_layer_19_41_0 26 cert44_layer_19_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 26 cert44_seen_19_41_1 = cert44_component_19_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_41_1 cert44_layer_19_41_1 25 cert44_layer_19_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 25 cert44_seen_19_41_2 = cert44_component_19_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_41_2 cert44_layer_19_41_2 24 cert44_layer_19_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 24 cert44_seen_19_41_3 = cert44_component_19_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_41_3 cert44_layer_19_41_3_eq 24

theorem cert44_step_19_41 :
    closedCollarIndexStepBool word fiber44 19 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_19_41)
    (by decide) (by decide)
    (by simpa [cert44_move_19_41] using cert44_component_19_41_eq)
    (by decide) (by decide) (by decide)

def cert44_move_20_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_20_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_20_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_20_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.p cert44_seen_20_0_0 = cert44_layer_20_0_0 := by
  decide

def cert44_seen_20_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_20_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_20_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.p cert44_seen_20_0_1 = cert44_layer_20_0_1 := by
  decide

def cert44_seen_20_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_20_0_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_20_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.p cert44_seen_20_0_2 = cert44_layer_20_0_2 := by
  decide

def cert44_seen_20_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_20_0_3 : List ChainEdge :=
  []

theorem cert44_layer_20_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.p cert44_seen_20_0_3 = cert44_layer_20_0_3 := by
  decide

theorem cert44_component_20_0_eq :
    closedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_20_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 20 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.p 27 cert44_seen_20_0_0 = cert44_component_20_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.p
    cert44_seen_20_0_0 cert44_layer_20_0_0 26 cert44_layer_20_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.p 26 cert44_seen_20_0_1 = cert44_component_20_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.p
    cert44_seen_20_0_1 cert44_layer_20_0_1 25 cert44_layer_20_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.p 25 cert44_seen_20_0_2 = cert44_component_20_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.p
    cert44_seen_20_0_2 cert44_layer_20_0_2 24 cert44_layer_20_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.p 24 cert44_seen_20_0_3 = cert44_component_20_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 20 []) LColor.r LColor.p
    cert44_seen_20_0_3 cert44_layer_20_0_3_eq 24

theorem cert44_step_20_0 :
    closedCollarIndexStepBool word fiber44 20 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_20_0)
    (by decide) (by decide)
    (by simpa [cert44_move_20_0] using cert44_component_20_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_20_42 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_20_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_seen_20_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_20_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_20_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_0 = cert44_layer_20_42_0 := by
  decide

def cert44_seen_20_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_20_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_20_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_1 = cert44_layer_20_42_1 := by
  decide

def cert44_seen_20_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_20_42_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_20_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_2 = cert44_layer_20_42_2 := by
  decide

def cert44_seen_20_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_20_42_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_20_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_3 = cert44_layer_20_42_3 := by
  decide

def cert44_seen_20_42_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_20_42_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_20_42_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_4 = cert44_layer_20_42_4 := by
  decide

def cert44_seen_20_42_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_20_42_5 : List ChainEdge :=
  []

theorem cert44_layer_20_42_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_42_5 = cert44_layer_20_42_5 := by
  decide

theorem cert44_component_20_42_eq :
    closedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_20_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 27 cert44_seen_20_42_0 = cert44_component_20_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_0 cert44_layer_20_42_0 26 cert44_layer_20_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 26 cert44_seen_20_42_1 = cert44_component_20_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_1 cert44_layer_20_42_1 25 cert44_layer_20_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 25 cert44_seen_20_42_2 = cert44_component_20_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_2 cert44_layer_20_42_2 24 cert44_layer_20_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 24 cert44_seen_20_42_3 = cert44_component_20_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_3 cert44_layer_20_42_3 23 cert44_layer_20_42_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 23 cert44_seen_20_42_4 = cert44_component_20_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_4 cert44_layer_20_42_4 22 cert44_layer_20_42_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 22 cert44_seen_20_42_5 = cert44_component_20_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_42_5 cert44_layer_20_42_5_eq 22

theorem cert44_step_20_42 :
    closedCollarIndexStepBool word fiber44 20 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_20_42)
    (by decide) (by decide)
    (by simpa [cert44_move_20_42] using cert44_component_20_42_eq)
    (by decide) (by decide) (by decide)

def cert44_move_21_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_21_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_21_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_21_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.p cert44_seen_21_1_0 = cert44_layer_21_1_0 := by
  decide

def cert44_seen_21_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_21_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_21_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.p cert44_seen_21_1_1 = cert44_layer_21_1_1 := by
  decide

def cert44_seen_21_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_21_1_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_21_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.p cert44_seen_21_1_2 = cert44_layer_21_1_2 := by
  decide

def cert44_seen_21_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_21_1_3 : List ChainEdge :=
  []

theorem cert44_layer_21_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.p cert44_seen_21_1_3 = cert44_layer_21_1_3 := by
  decide

theorem cert44_component_21_1_eq :
    closedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_21_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 21 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.p 27 cert44_seen_21_1_0 = cert44_component_21_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.p
    cert44_seen_21_1_0 cert44_layer_21_1_0 26 cert44_layer_21_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.p 26 cert44_seen_21_1_1 = cert44_component_21_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.p
    cert44_seen_21_1_1 cert44_layer_21_1_1 25 cert44_layer_21_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.p 25 cert44_seen_21_1_2 = cert44_component_21_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.p
    cert44_seen_21_1_2 cert44_layer_21_1_2 24 cert44_layer_21_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.p 24 cert44_seen_21_1_3 = cert44_component_21_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 21 []) LColor.r LColor.p
    cert44_seen_21_1_3 cert44_layer_21_1_3_eq 24

theorem cert44_step_21_1 :
    closedCollarIndexStepBool word fiber44 21 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_21_1)
    (by decide) (by decide)
    (by simpa [cert44_move_21_1] using cert44_component_21_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_21_43 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_21_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_21_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_21_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_21_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_0 = cert44_layer_21_43_0 := by
  decide

def cert44_seen_21_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_21_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_21_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_1 = cert44_layer_21_43_1 := by
  decide

def cert44_seen_21_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_21_43_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_21_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_2 = cert44_layer_21_43_2 := by
  decide

def cert44_seen_21_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_21_43_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_21_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_3 = cert44_layer_21_43_3 := by
  decide

def cert44_seen_21_43_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_21_43_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_21_43_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_4 = cert44_layer_21_43_4 := by
  decide

def cert44_seen_21_43_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_21_43_5 : List ChainEdge :=
  []

theorem cert44_layer_21_43_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_43_5 = cert44_layer_21_43_5 := by
  decide

theorem cert44_component_21_43_eq :
    closedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_21_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 27 cert44_seen_21_43_0 = cert44_component_21_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_0 cert44_layer_21_43_0 26 cert44_layer_21_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 26 cert44_seen_21_43_1 = cert44_component_21_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_1 cert44_layer_21_43_1 25 cert44_layer_21_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 25 cert44_seen_21_43_2 = cert44_component_21_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_2 cert44_layer_21_43_2 24 cert44_layer_21_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 24 cert44_seen_21_43_3 = cert44_component_21_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_3 cert44_layer_21_43_3 23 cert44_layer_21_43_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 23 cert44_seen_21_43_4 = cert44_component_21_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_4 cert44_layer_21_43_4 22 cert44_layer_21_43_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 22 cert44_seen_21_43_5 = cert44_component_21_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_43_5 cert44_layer_21_43_5_eq 22

theorem cert44_step_21_43 :
    closedCollarIndexStepBool word fiber44 21 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_21_43)
    (by decide) (by decide)
    (by simpa [cert44_move_21_43] using cert44_component_21_43_eq)
    (by decide) (by decide) (by decide)

def cert44_move_22_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_22_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_22_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_22_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.p cert44_seen_22_2_0 = cert44_layer_22_2_0 := by
  decide

def cert44_seen_22_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_22_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_22_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.p cert44_seen_22_2_1 = cert44_layer_22_2_1 := by
  decide

def cert44_seen_22_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_22_2_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_22_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.p cert44_seen_22_2_2 = cert44_layer_22_2_2 := by
  decide

def cert44_seen_22_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_22_2_3 : List ChainEdge :=
  []

theorem cert44_layer_22_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.p cert44_seen_22_2_3 = cert44_layer_22_2_3 := by
  decide

theorem cert44_component_22_2_eq :
    closedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_22_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 22 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.p 27 cert44_seen_22_2_0 = cert44_component_22_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 22 []) LColor.r LColor.p
    cert44_seen_22_2_0 cert44_layer_22_2_0 26 cert44_layer_22_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.p 26 cert44_seen_22_2_1 = cert44_component_22_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 22 []) LColor.r LColor.p
    cert44_seen_22_2_1 cert44_layer_22_2_1 25 cert44_layer_22_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.p 25 cert44_seen_22_2_2 = cert44_component_22_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 22 []) LColor.r LColor.p
    cert44_seen_22_2_2 cert44_layer_22_2_2 24 cert44_layer_22_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.p 24 cert44_seen_22_2_3 = cert44_component_22_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 22 []) LColor.r LColor.p
    cert44_seen_22_2_3 cert44_layer_22_2_3_eq 24

theorem cert44_step_22_2 :
    closedCollarIndexStepBool word fiber44 22 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_22_2)
    (by decide) (by decide)
    (by simpa [cert44_move_22_2] using cert44_component_22_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_23_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_23_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_23_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_23_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_23_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.p cert44_seen_23_3_0 = cert44_layer_23_3_0 := by
  decide

def cert44_seen_23_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_23_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_23_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.p cert44_seen_23_3_1 = cert44_layer_23_3_1 := by
  decide

def cert44_seen_23_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_23_3_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_23_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.p cert44_seen_23_3_2 = cert44_layer_23_3_2 := by
  decide

def cert44_seen_23_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_23_3_3 : List ChainEdge :=
  []

theorem cert44_layer_23_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.p cert44_seen_23_3_3 = cert44_layer_23_3_3 := by
  decide

theorem cert44_component_23_3_eq :
    closedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_23_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 23 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.p 27 cert44_seen_23_3_0 = cert44_component_23_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 23 []) LColor.r LColor.p
    cert44_seen_23_3_0 cert44_layer_23_3_0 26 cert44_layer_23_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.p 26 cert44_seen_23_3_1 = cert44_component_23_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 23 []) LColor.r LColor.p
    cert44_seen_23_3_1 cert44_layer_23_3_1 25 cert44_layer_23_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.p 25 cert44_seen_23_3_2 = cert44_component_23_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 23 []) LColor.r LColor.p
    cert44_seen_23_3_2 cert44_layer_23_3_2 24 cert44_layer_23_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.p 24 cert44_seen_23_3_3 = cert44_component_23_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 23 []) LColor.r LColor.p
    cert44_seen_23_3_3 cert44_layer_23_3_3_eq 24

theorem cert44_step_23_3 :
    closedCollarIndexStepBool word fiber44 23 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_23_3)
    (by decide) (by decide)
    (by simpa [cert44_move_23_3] using cert44_component_23_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_24_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_24_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_24_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.b cert44_seen_24_0_0 = cert44_layer_24_0_0 := by
  decide

def cert44_seen_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_24_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_24_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.b cert44_seen_24_0_1 = cert44_layer_24_0_1 := by
  decide

def cert44_seen_24_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_24_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_24_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.b cert44_seen_24_0_2 = cert44_layer_24_0_2 := by
  decide

def cert44_seen_24_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_24_0_3 : List ChainEdge :=
  []

theorem cert44_layer_24_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.b cert44_seen_24_0_3 = cert44_layer_24_0_3 := by
  decide

theorem cert44_component_24_0_eq :
    closedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_24_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 24 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.b 27 cert44_seen_24_0_0 = cert44_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.b
    cert44_seen_24_0_0 cert44_layer_24_0_0 26 cert44_layer_24_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.b 26 cert44_seen_24_0_1 = cert44_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.b
    cert44_seen_24_0_1 cert44_layer_24_0_1 25 cert44_layer_24_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.b 25 cert44_seen_24_0_2 = cert44_component_24_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.b
    cert44_seen_24_0_2 cert44_layer_24_0_2 24 cert44_layer_24_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.b 24 cert44_seen_24_0_3 = cert44_component_24_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 24 []) LColor.r LColor.b
    cert44_seen_24_0_3 cert44_layer_24_0_3_eq 24

theorem cert44_step_24_0 :
    closedCollarIndexStepBool word fiber44 24 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_24_0)
    (by decide) (by decide)
    (by simpa [cert44_move_24_0] using cert44_component_24_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_25_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_25_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_25_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.b cert44_seen_25_1_0 = cert44_layer_25_1_0 := by
  decide

def cert44_seen_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_25_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_25_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.b cert44_seen_25_1_1 = cert44_layer_25_1_1 := by
  decide

def cert44_seen_25_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_25_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_25_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.b cert44_seen_25_1_2 = cert44_layer_25_1_2 := by
  decide

def cert44_seen_25_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_25_1_3 : List ChainEdge :=
  []

theorem cert44_layer_25_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.b cert44_seen_25_1_3 = cert44_layer_25_1_3 := by
  decide

theorem cert44_component_25_1_eq :
    closedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_25_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 25 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.b 27 cert44_seen_25_1_0 = cert44_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.b
    cert44_seen_25_1_0 cert44_layer_25_1_0 26 cert44_layer_25_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.b 26 cert44_seen_25_1_1 = cert44_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.b
    cert44_seen_25_1_1 cert44_layer_25_1_1 25 cert44_layer_25_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.b 25 cert44_seen_25_1_2 = cert44_component_25_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.b
    cert44_seen_25_1_2 cert44_layer_25_1_2 24 cert44_layer_25_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.b 24 cert44_seen_25_1_3 = cert44_component_25_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 25 []) LColor.r LColor.b
    cert44_seen_25_1_3 cert44_layer_25_1_3_eq 24

theorem cert44_step_25_1 :
    closedCollarIndexStepBool word fiber44 25 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_25_1)
    (by decide) (by decide)
    (by simpa [cert44_move_25_1] using cert44_component_25_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_26_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_26_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_26_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.b cert44_seen_26_2_0 = cert44_layer_26_2_0 := by
  decide

def cert44_seen_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_26_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_26_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.b cert44_seen_26_2_1 = cert44_layer_26_2_1 := by
  decide

def cert44_seen_26_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_26_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_26_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.b cert44_seen_26_2_2 = cert44_layer_26_2_2 := by
  decide

def cert44_seen_26_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_26_2_3 : List ChainEdge :=
  []

theorem cert44_layer_26_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.b cert44_seen_26_2_3 = cert44_layer_26_2_3 := by
  decide

theorem cert44_component_26_2_eq :
    closedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_26_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 26 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.b 27 cert44_seen_26_2_0 = cert44_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.b
    cert44_seen_26_2_0 cert44_layer_26_2_0 26 cert44_layer_26_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.b 26 cert44_seen_26_2_1 = cert44_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.b
    cert44_seen_26_2_1 cert44_layer_26_2_1 25 cert44_layer_26_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.b 25 cert44_seen_26_2_2 = cert44_component_26_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.b
    cert44_seen_26_2_2 cert44_layer_26_2_2 24 cert44_layer_26_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.b 24 cert44_seen_26_2_3 = cert44_component_26_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 26 []) LColor.r LColor.b
    cert44_seen_26_2_3 cert44_layer_26_2_3_eq 24

theorem cert44_step_26_2 :
    closedCollarIndexStepBool word fiber44 26 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_26_2)
    (by decide) (by decide)
    (by simpa [cert44_move_26_2] using cert44_component_26_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_26_36 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_26_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_seen_26_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_26_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_26_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_0 = cert44_layer_26_36_0 := by
  decide

def cert44_seen_26_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_26_36_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_26_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_1 = cert44_layer_26_36_1 := by
  decide

def cert44_seen_26_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_26_36_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_26_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_2 = cert44_layer_26_36_2 := by
  decide

def cert44_seen_26_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_26_36_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_26_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_3 = cert44_layer_26_36_3 := by
  decide

def cert44_seen_26_36_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_26_36_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert44_layer_26_36_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_4 = cert44_layer_26_36_4 := by
  decide

def cert44_seen_26_36_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_26_36_5 : List ChainEdge :=
  []

theorem cert44_layer_26_36_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.b LColor.p cert44_seen_26_36_5 = cert44_layer_26_36_5 := by
  decide

theorem cert44_component_26_36_eq :
    closedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_26_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 26 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 27 cert44_seen_26_36_0 = cert44_component_26_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_0 cert44_layer_26_36_0 26 cert44_layer_26_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 26 cert44_seen_26_36_1 = cert44_component_26_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_1 cert44_layer_26_36_1 25 cert44_layer_26_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 25 cert44_seen_26_36_2 = cert44_component_26_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_2 cert44_layer_26_36_2 24 cert44_layer_26_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 24 cert44_seen_26_36_3 = cert44_component_26_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_3 cert44_layer_26_36_3 23 cert44_layer_26_36_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 23 cert44_seen_26_36_4 = cert44_component_26_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_4 cert44_layer_26_36_4 22 cert44_layer_26_36_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.b LColor.p 22 cert44_seen_26_36_5 = cert44_component_26_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 26 []) LColor.b LColor.p
    cert44_seen_26_36_5 cert44_layer_26_36_5_eq 22

theorem cert44_step_26_36 :
    closedCollarIndexStepBool word fiber44 26 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_26_36)
    (by decide) (by decide)
    (by simpa [cert44_move_26_36] using cert44_component_26_36_eq)
    (by decide) (by decide) (by decide)

def cert44_move_27_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_27_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_27_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.b cert44_seen_27_3_0 = cert44_layer_27_3_0 := by
  decide

def cert44_seen_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_27_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_27_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.b cert44_seen_27_3_1 = cert44_layer_27_3_1 := by
  decide

def cert44_seen_27_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_27_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_27_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.b cert44_seen_27_3_2 = cert44_layer_27_3_2 := by
  decide

def cert44_seen_27_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_27_3_3 : List ChainEdge :=
  []

theorem cert44_layer_27_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.b cert44_seen_27_3_3 = cert44_layer_27_3_3 := by
  decide

theorem cert44_component_27_3_eq :
    closedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_27_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 27 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.b 27 cert44_seen_27_3_0 = cert44_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.b
    cert44_seen_27_3_0 cert44_layer_27_3_0 26 cert44_layer_27_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.b 26 cert44_seen_27_3_1 = cert44_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.b
    cert44_seen_27_3_1 cert44_layer_27_3_1 25 cert44_layer_27_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.b 25 cert44_seen_27_3_2 = cert44_component_27_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.b
    cert44_seen_27_3_2 cert44_layer_27_3_2 24 cert44_layer_27_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.b 24 cert44_seen_27_3_3 = cert44_component_27_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 27 []) LColor.r LColor.b
    cert44_seen_27_3_3 cert44_layer_27_3_3_eq 24

theorem cert44_step_27_3 :
    closedCollarIndexStepBool word fiber44 27 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_27_3)
    (by decide) (by decide)
    (by simpa [cert44_move_27_3] using cert44_component_27_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_27_37 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_27_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_seen_27_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_27_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_27_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_0 = cert44_layer_27_37_0 := by
  decide

def cert44_seen_27_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_27_37_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_27_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_1 = cert44_layer_27_37_1 := by
  decide

def cert44_seen_27_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_27_37_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_27_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_2 = cert44_layer_27_37_2 := by
  decide

def cert44_seen_27_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_27_37_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_27_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_3 = cert44_layer_27_37_3 := by
  decide

def cert44_seen_27_37_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_27_37_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert44_layer_27_37_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_4 = cert44_layer_27_37_4 := by
  decide

def cert44_seen_27_37_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_27_37_5 : List ChainEdge :=
  []

theorem cert44_layer_27_37_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.b LColor.p cert44_seen_27_37_5 = cert44_layer_27_37_5 := by
  decide

theorem cert44_component_27_37_eq :
    closedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_27_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 27 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 27 cert44_seen_27_37_0 = cert44_component_27_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_0 cert44_layer_27_37_0 26 cert44_layer_27_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 26 cert44_seen_27_37_1 = cert44_component_27_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_1 cert44_layer_27_37_1 25 cert44_layer_27_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 25 cert44_seen_27_37_2 = cert44_component_27_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_2 cert44_layer_27_37_2 24 cert44_layer_27_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 24 cert44_seen_27_37_3 = cert44_component_27_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_3 cert44_layer_27_37_3 23 cert44_layer_27_37_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 23 cert44_seen_27_37_4 = cert44_component_27_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_4 cert44_layer_27_37_4 22 cert44_layer_27_37_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.b LColor.p 22 cert44_seen_27_37_5 = cert44_component_27_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 27 []) LColor.b LColor.p
    cert44_seen_27_37_5 cert44_layer_27_37_5_eq 22

theorem cert44_step_27_37 :
    closedCollarIndexStepBool word fiber44 27 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_27_37)
    (by decide) (by decide)
    (by simpa [cert44_move_27_37] using cert44_component_27_37_eq)
    (by decide) (by decide) (by decide)

def cert44_move_28_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_28_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_28_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_28_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_28_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.b cert44_seen_28_4_0 = cert44_layer_28_4_0 := by
  decide

def cert44_seen_28_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_28_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_28_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.b cert44_seen_28_4_1 = cert44_layer_28_4_1 := by
  decide

def cert44_seen_28_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_28_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_28_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.b cert44_seen_28_4_2 = cert44_layer_28_4_2 := by
  decide

def cert44_seen_28_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_28_4_3 : List ChainEdge :=
  []

theorem cert44_layer_28_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.b cert44_seen_28_4_3 = cert44_layer_28_4_3 := by
  decide

theorem cert44_component_28_4_eq :
    closedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_28_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 28 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.b 27 cert44_seen_28_4_0 = cert44_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.b
    cert44_seen_28_4_0 cert44_layer_28_4_0 26 cert44_layer_28_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.b 26 cert44_seen_28_4_1 = cert44_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.b
    cert44_seen_28_4_1 cert44_layer_28_4_1 25 cert44_layer_28_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.b 25 cert44_seen_28_4_2 = cert44_component_28_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.b
    cert44_seen_28_4_2 cert44_layer_28_4_2 24 cert44_layer_28_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.b 24 cert44_seen_28_4_3 = cert44_component_28_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 28 []) LColor.r LColor.b
    cert44_seen_28_4_3 cert44_layer_28_4_3_eq 24

theorem cert44_step_28_4 :
    closedCollarIndexStepBool word fiber44 28 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_28_4)
    (by decide) (by decide)
    (by simpa [cert44_move_28_4] using cert44_component_28_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_28_38 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_28_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_28_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_28_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_28_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.b LColor.p cert44_seen_28_38_0 = cert44_layer_28_38_0 := by
  decide

def cert44_seen_28_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_28_38_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_28_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.b LColor.p cert44_seen_28_38_1 = cert44_layer_28_38_1 := by
  decide

def cert44_seen_28_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_28_38_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_28_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.b LColor.p cert44_seen_28_38_2 = cert44_layer_28_38_2 := by
  decide

def cert44_seen_28_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_28_38_3 : List ChainEdge :=
  []

theorem cert44_layer_28_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.b LColor.p cert44_seen_28_38_3 = cert44_layer_28_38_3 := by
  decide

theorem cert44_component_28_38_eq :
    closedCollarComponent word (listGetD fiber44 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_28_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 28 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.b LColor.p 27 cert44_seen_28_38_0 = cert44_component_28_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.b LColor.p
    cert44_seen_28_38_0 cert44_layer_28_38_0 26 cert44_layer_28_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.b LColor.p 26 cert44_seen_28_38_1 = cert44_component_28_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.b LColor.p
    cert44_seen_28_38_1 cert44_layer_28_38_1 25 cert44_layer_28_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.b LColor.p 25 cert44_seen_28_38_2 = cert44_component_28_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.b LColor.p
    cert44_seen_28_38_2 cert44_layer_28_38_2 24 cert44_layer_28_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.b LColor.p 24 cert44_seen_28_38_3 = cert44_component_28_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 28 []) LColor.b LColor.p
    cert44_seen_28_38_3 cert44_layer_28_38_3_eq 24

theorem cert44_step_28_38 :
    closedCollarIndexStepBool word fiber44 28 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_28_38)
    (by decide) (by decide)
    (by simpa [cert44_move_28_38] using cert44_component_28_38_eq)
    (by decide) (by decide) (by decide)

def cert44_move_29_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_29_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_29_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_29_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_29_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.b cert44_seen_29_5_0 = cert44_layer_29_5_0 := by
  decide

def cert44_seen_29_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_29_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_29_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.b cert44_seen_29_5_1 = cert44_layer_29_5_1 := by
  decide

def cert44_seen_29_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_29_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_29_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.b cert44_seen_29_5_2 = cert44_layer_29_5_2 := by
  decide

def cert44_seen_29_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_29_5_3 : List ChainEdge :=
  []

theorem cert44_layer_29_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.b cert44_seen_29_5_3 = cert44_layer_29_5_3 := by
  decide

theorem cert44_component_29_5_eq :
    closedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_29_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 29 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.b 27 cert44_seen_29_5_0 = cert44_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.b
    cert44_seen_29_5_0 cert44_layer_29_5_0 26 cert44_layer_29_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.b 26 cert44_seen_29_5_1 = cert44_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.b
    cert44_seen_29_5_1 cert44_layer_29_5_1 25 cert44_layer_29_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.b 25 cert44_seen_29_5_2 = cert44_component_29_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.b
    cert44_seen_29_5_2 cert44_layer_29_5_2 24 cert44_layer_29_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.b 24 cert44_seen_29_5_3 = cert44_component_29_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 29 []) LColor.r LColor.b
    cert44_seen_29_5_3 cert44_layer_29_5_3_eq 24

theorem cert44_step_29_5 :
    closedCollarIndexStepBool word fiber44 29 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_29_5)
    (by decide) (by decide)
    (by simpa [cert44_move_29_5] using cert44_component_29_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_29_39 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_29_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_29_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_29_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_29_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.b LColor.p cert44_seen_29_39_0 = cert44_layer_29_39_0 := by
  decide

def cert44_seen_29_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_29_39_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_29_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.b LColor.p cert44_seen_29_39_1 = cert44_layer_29_39_1 := by
  decide

def cert44_seen_29_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_29_39_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_29_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.b LColor.p cert44_seen_29_39_2 = cert44_layer_29_39_2 := by
  decide

def cert44_seen_29_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_29_39_3 : List ChainEdge :=
  []

theorem cert44_layer_29_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.b LColor.p cert44_seen_29_39_3 = cert44_layer_29_39_3 := by
  decide

theorem cert44_component_29_39_eq :
    closedCollarComponent word (listGetD fiber44 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_29_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 29 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.b LColor.p 27 cert44_seen_29_39_0 = cert44_component_29_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.b LColor.p
    cert44_seen_29_39_0 cert44_layer_29_39_0 26 cert44_layer_29_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.b LColor.p 26 cert44_seen_29_39_1 = cert44_component_29_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.b LColor.p
    cert44_seen_29_39_1 cert44_layer_29_39_1 25 cert44_layer_29_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.b LColor.p 25 cert44_seen_29_39_2 = cert44_component_29_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.b LColor.p
    cert44_seen_29_39_2 cert44_layer_29_39_2 24 cert44_layer_29_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.b LColor.p 24 cert44_seen_29_39_3 = cert44_component_29_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 29 []) LColor.b LColor.p
    cert44_seen_29_39_3 cert44_layer_29_39_3_eq 24

theorem cert44_step_29_39 :
    closedCollarIndexStepBool word fiber44 29 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_29_39)
    (by decide) (by decide)
    (by simpa [cert44_move_29_39] using cert44_component_29_39_eq)
    (by decide) (by decide) (by decide)

def cert44_move_30_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_30_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_30_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_30_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.r LColor.b cert44_seen_30_6_0 = cert44_layer_30_6_0 := by
  decide

def cert44_seen_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_30_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_30_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.r LColor.b cert44_seen_30_6_1 = cert44_layer_30_6_1 := by
  decide

def cert44_seen_30_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_30_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_30_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.r LColor.b cert44_seen_30_6_2 = cert44_layer_30_6_2 := by
  decide

def cert44_seen_30_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_30_6_3 : List ChainEdge :=
  []

theorem cert44_layer_30_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.r LColor.b cert44_seen_30_6_3 = cert44_layer_30_6_3 := by
  decide

theorem cert44_component_30_6_eq :
    closedCollarComponent word (listGetD fiber44 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_30_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 30 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.r LColor.b 27 cert44_seen_30_6_0 = cert44_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 30 []) LColor.r LColor.b
    cert44_seen_30_6_0 cert44_layer_30_6_0 26 cert44_layer_30_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.r LColor.b 26 cert44_seen_30_6_1 = cert44_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 30 []) LColor.r LColor.b
    cert44_seen_30_6_1 cert44_layer_30_6_1 25 cert44_layer_30_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.r LColor.b 25 cert44_seen_30_6_2 = cert44_component_30_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 30 []) LColor.r LColor.b
    cert44_seen_30_6_2 cert44_layer_30_6_2 24 cert44_layer_30_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.r LColor.b 24 cert44_seen_30_6_3 = cert44_component_30_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 30 []) LColor.r LColor.b
    cert44_seen_30_6_3 cert44_layer_30_6_3_eq 24

theorem cert44_step_30_6 :
    closedCollarIndexStepBool word fiber44 30 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_30_6)
    (by decide) (by decide)
    (by simpa [cert44_move_30_6] using cert44_component_30_6_eq)
    (by decide) (by decide) (by decide)

def cert44_move_31_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_31_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_31_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_31_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.r LColor.b cert44_seen_31_7_0 = cert44_layer_31_7_0 := by
  decide

def cert44_seen_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_31_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_31_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.r LColor.b cert44_seen_31_7_1 = cert44_layer_31_7_1 := by
  decide

def cert44_seen_31_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_31_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_31_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.r LColor.b cert44_seen_31_7_2 = cert44_layer_31_7_2 := by
  decide

def cert44_seen_31_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_31_7_3 : List ChainEdge :=
  []

theorem cert44_layer_31_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.r LColor.b cert44_seen_31_7_3 = cert44_layer_31_7_3 := by
  decide

theorem cert44_component_31_7_eq :
    closedCollarComponent word (listGetD fiber44 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_31_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 31 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.r LColor.b 27 cert44_seen_31_7_0 = cert44_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 31 []) LColor.r LColor.b
    cert44_seen_31_7_0 cert44_layer_31_7_0 26 cert44_layer_31_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.r LColor.b 26 cert44_seen_31_7_1 = cert44_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 31 []) LColor.r LColor.b
    cert44_seen_31_7_1 cert44_layer_31_7_1 25 cert44_layer_31_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.r LColor.b 25 cert44_seen_31_7_2 = cert44_component_31_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 31 []) LColor.r LColor.b
    cert44_seen_31_7_2 cert44_layer_31_7_2 24 cert44_layer_31_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.r LColor.b 24 cert44_seen_31_7_3 = cert44_component_31_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 31 []) LColor.r LColor.b
    cert44_seen_31_7_3 cert44_layer_31_7_3_eq 24

theorem cert44_step_31_7 :
    closedCollarIndexStepBool word fiber44 31 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_31_7)
    (by decide) (by decide)
    (by simpa [cert44_move_31_7] using cert44_component_31_7_eq)
    (by decide) (by decide) (by decide)

def cert44_move_32_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_32_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_32_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_32_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.r LColor.b cert44_seen_32_8_0 = cert44_layer_32_8_0 := by
  decide

def cert44_seen_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_32_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_32_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.r LColor.b cert44_seen_32_8_1 = cert44_layer_32_8_1 := by
  decide

def cert44_seen_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_32_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_32_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.r LColor.b cert44_seen_32_8_2 = cert44_layer_32_8_2 := by
  decide

def cert44_seen_32_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_32_8_3 : List ChainEdge :=
  []

theorem cert44_layer_32_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.r LColor.b cert44_seen_32_8_3 = cert44_layer_32_8_3 := by
  decide

theorem cert44_component_32_8_eq :
    closedCollarComponent word (listGetD fiber44 32 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_32_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 32 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.r LColor.b 27 cert44_seen_32_8_0 = cert44_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 32 []) LColor.r LColor.b
    cert44_seen_32_8_0 cert44_layer_32_8_0 26 cert44_layer_32_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.r LColor.b 26 cert44_seen_32_8_1 = cert44_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 32 []) LColor.r LColor.b
    cert44_seen_32_8_1 cert44_layer_32_8_1 25 cert44_layer_32_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.r LColor.b 25 cert44_seen_32_8_2 = cert44_component_32_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 32 []) LColor.r LColor.b
    cert44_seen_32_8_2 cert44_layer_32_8_2 24 cert44_layer_32_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.r LColor.b 24 cert44_seen_32_8_3 = cert44_component_32_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 32 []) LColor.r LColor.b
    cert44_seen_32_8_3 cert44_layer_32_8_3_eq 24

theorem cert44_step_32_8 :
    closedCollarIndexStepBool word fiber44 32 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_32_8)
    (by decide) (by decide)
    (by simpa [cert44_move_32_8] using cert44_component_32_8_eq)
    (by decide) (by decide) (by decide)

def cert44_move_33_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_33_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_33_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_33_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.r LColor.b cert44_seen_33_9_0 = cert44_layer_33_9_0 := by
  decide

def cert44_seen_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_33_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_33_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.r LColor.b cert44_seen_33_9_1 = cert44_layer_33_9_1 := by
  decide

def cert44_seen_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_33_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_33_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.r LColor.b cert44_seen_33_9_2 = cert44_layer_33_9_2 := by
  decide

def cert44_seen_33_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_33_9_3 : List ChainEdge :=
  []

theorem cert44_layer_33_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.r LColor.b cert44_seen_33_9_3 = cert44_layer_33_9_3 := by
  decide

theorem cert44_component_33_9_eq :
    closedCollarComponent word (listGetD fiber44 33 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_33_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 33 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.r LColor.b 27 cert44_seen_33_9_0 = cert44_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 33 []) LColor.r LColor.b
    cert44_seen_33_9_0 cert44_layer_33_9_0 26 cert44_layer_33_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.r LColor.b 26 cert44_seen_33_9_1 = cert44_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 33 []) LColor.r LColor.b
    cert44_seen_33_9_1 cert44_layer_33_9_1 25 cert44_layer_33_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.r LColor.b 25 cert44_seen_33_9_2 = cert44_component_33_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 33 []) LColor.r LColor.b
    cert44_seen_33_9_2 cert44_layer_33_9_2 24 cert44_layer_33_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.r LColor.b 24 cert44_seen_33_9_3 = cert44_component_33_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 33 []) LColor.r LColor.b
    cert44_seen_33_9_3 cert44_layer_33_9_3_eq 24

theorem cert44_step_33_9 :
    closedCollarIndexStepBool word fiber44 33 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_33_9)
    (by decide) (by decide)
    (by simpa [cert44_move_33_9] using cert44_component_33_9_eq)
    (by decide) (by decide) (by decide)

def cert44_move_34_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_34_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_34_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_34_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.r LColor.b cert44_seen_34_10_0 = cert44_layer_34_10_0 := by
  decide

def cert44_seen_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_34_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_34_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.r LColor.b cert44_seen_34_10_1 = cert44_layer_34_10_1 := by
  decide

def cert44_seen_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_34_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_34_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.r LColor.b cert44_seen_34_10_2 = cert44_layer_34_10_2 := by
  decide

def cert44_seen_34_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_34_10_3 : List ChainEdge :=
  []

theorem cert44_layer_34_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.r LColor.b cert44_seen_34_10_3 = cert44_layer_34_10_3 := by
  decide

theorem cert44_component_34_10_eq :
    closedCollarComponent word (listGetD fiber44 34 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_34_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 34 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.r LColor.b 27 cert44_seen_34_10_0 = cert44_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 34 []) LColor.r LColor.b
    cert44_seen_34_10_0 cert44_layer_34_10_0 26 cert44_layer_34_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.r LColor.b 26 cert44_seen_34_10_1 = cert44_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 34 []) LColor.r LColor.b
    cert44_seen_34_10_1 cert44_layer_34_10_1 25 cert44_layer_34_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.r LColor.b 25 cert44_seen_34_10_2 = cert44_component_34_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 34 []) LColor.r LColor.b
    cert44_seen_34_10_2 cert44_layer_34_10_2 24 cert44_layer_34_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.r LColor.b 24 cert44_seen_34_10_3 = cert44_component_34_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 34 []) LColor.r LColor.b
    cert44_seen_34_10_3 cert44_layer_34_10_3_eq 24

theorem cert44_step_34_10 :
    closedCollarIndexStepBool word fiber44 34 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_34_10)
    (by decide) (by decide)
    (by simpa [cert44_move_34_10] using cert44_component_34_10_eq)
    (by decide) (by decide) (by decide)

def cert44_move_35_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_35_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_seen_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_35_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_35_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.r LColor.b cert44_seen_35_11_0 = cert44_layer_35_11_0 := by
  decide

def cert44_seen_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_35_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_35_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.r LColor.b cert44_seen_35_11_1 = cert44_layer_35_11_1 := by
  decide

def cert44_seen_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_35_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

theorem cert44_layer_35_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.r LColor.b cert44_seen_35_11_2 = cert44_layer_35_11_2 := by
  decide

def cert44_seen_35_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 0, edge := TauEdge.B6 }]

def cert44_layer_35_11_3 : List ChainEdge :=
  []

theorem cert44_layer_35_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.r LColor.b cert44_seen_35_11_3 = cert44_layer_35_11_3 := by
  decide

theorem cert44_component_35_11_eq :
    closedCollarComponent word (listGetD fiber44 35 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_35_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 35 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.r LColor.b 27 cert44_seen_35_11_0 = cert44_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 35 []) LColor.r LColor.b
    cert44_seen_35_11_0 cert44_layer_35_11_0 26 cert44_layer_35_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.r LColor.b 26 cert44_seen_35_11_1 = cert44_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 35 []) LColor.r LColor.b
    cert44_seen_35_11_1 cert44_layer_35_11_1 25 cert44_layer_35_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.r LColor.b 25 cert44_seen_35_11_2 = cert44_component_35_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 35 []) LColor.r LColor.b
    cert44_seen_35_11_2 cert44_layer_35_11_2 24 cert44_layer_35_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.r LColor.b 24 cert44_seen_35_11_3 = cert44_component_35_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 35 []) LColor.r LColor.b
    cert44_seen_35_11_3 cert44_layer_35_11_3_eq 24

theorem cert44_step_35_11 :
    closedCollarIndexStepBool word fiber44 35 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_35_11)
    (by decide) (by decide)
    (by simpa [cert44_move_35_11] using cert44_component_35_11_eq)
    (by decide) (by decide) (by decide)

def cert44_move_36_26 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_36_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_seen_36_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_36_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_36_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_0 = cert44_layer_36_26_0 := by
  decide

def cert44_seen_36_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_36_26_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_36_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_1 = cert44_layer_36_26_1 := by
  decide

def cert44_seen_36_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_36_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_36_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_2 = cert44_layer_36_26_2 := by
  decide

def cert44_seen_36_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_36_26_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_36_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_3 = cert44_layer_36_26_3 := by
  decide

def cert44_seen_36_26_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_36_26_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert44_layer_36_26_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_4 = cert44_layer_36_26_4 := by
  decide

def cert44_seen_36_26_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_36_26_5 : List ChainEdge :=
  []

theorem cert44_layer_36_26_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.b LColor.p cert44_seen_36_26_5 = cert44_layer_36_26_5 := by
  decide

theorem cert44_component_36_26_eq :
    closedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_36_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 36 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 27 cert44_seen_36_26_0 = cert44_component_36_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_0 cert44_layer_36_26_0 26 cert44_layer_36_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 26 cert44_seen_36_26_1 = cert44_component_36_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_1 cert44_layer_36_26_1 25 cert44_layer_36_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 25 cert44_seen_36_26_2 = cert44_component_36_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_2 cert44_layer_36_26_2 24 cert44_layer_36_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 24 cert44_seen_36_26_3 = cert44_component_36_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_3 cert44_layer_36_26_3 23 cert44_layer_36_26_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 23 cert44_seen_36_26_4 = cert44_component_36_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_4 cert44_layer_36_26_4 22 cert44_layer_36_26_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.b LColor.p 22 cert44_seen_36_26_5 = cert44_component_36_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 36 []) LColor.b LColor.p
    cert44_seen_36_26_5 cert44_layer_36_26_5_eq 22

theorem cert44_step_36_26 :
    closedCollarIndexStepBool word fiber44 36 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_36_26)
    (by decide) (by decide)
    (by simpa [cert44_move_36_26] using cert44_component_36_26_eq)
    (by decide) (by decide) (by decide)

def cert44_move_37_27 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_37_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_seen_37_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_37_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_37_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_0 = cert44_layer_37_27_0 := by
  decide

def cert44_seen_37_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_37_27_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_37_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_1 = cert44_layer_37_27_1 := by
  decide

def cert44_seen_37_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_37_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_37_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_2 = cert44_layer_37_27_2 := by
  decide

def cert44_seen_37_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_37_27_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_37_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_3 = cert44_layer_37_27_3 := by
  decide

def cert44_seen_37_27_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_37_27_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }]

theorem cert44_layer_37_27_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_4 = cert44_layer_37_27_4 := by
  decide

def cert44_seen_37_27_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F4F5 }]

def cert44_layer_37_27_5 : List ChainEdge :=
  []

theorem cert44_layer_37_27_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.b LColor.p cert44_seen_37_27_5 = cert44_layer_37_27_5 := by
  decide

theorem cert44_component_37_27_eq :
    closedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_37_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 37 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 27 cert44_seen_37_27_0 = cert44_component_37_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_0 cert44_layer_37_27_0 26 cert44_layer_37_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 26 cert44_seen_37_27_1 = cert44_component_37_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_1 cert44_layer_37_27_1 25 cert44_layer_37_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 25 cert44_seen_37_27_2 = cert44_component_37_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_2 cert44_layer_37_27_2 24 cert44_layer_37_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 24 cert44_seen_37_27_3 = cert44_component_37_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_3 cert44_layer_37_27_3 23 cert44_layer_37_27_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 23 cert44_seen_37_27_4 = cert44_component_37_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_4 cert44_layer_37_27_4 22 cert44_layer_37_27_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.b LColor.p 22 cert44_seen_37_27_5 = cert44_component_37_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 37 []) LColor.b LColor.p
    cert44_seen_37_27_5 cert44_layer_37_27_5_eq 22

theorem cert44_step_37_27 :
    closedCollarIndexStepBool word fiber44 37 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_37_27)
    (by decide) (by decide)
    (by simpa [cert44_move_37_27] using cert44_component_37_27_eq)
    (by decide) (by decide) (by decide)

def cert44_move_38_28 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_38_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_38_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_38_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_38_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.b LColor.p cert44_seen_38_28_0 = cert44_layer_38_28_0 := by
  decide

def cert44_seen_38_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_38_28_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_38_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.b LColor.p cert44_seen_38_28_1 = cert44_layer_38_28_1 := by
  decide

def cert44_seen_38_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_38_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_38_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.b LColor.p cert44_seen_38_28_2 = cert44_layer_38_28_2 := by
  decide

def cert44_seen_38_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_38_28_3 : List ChainEdge :=
  []

theorem cert44_layer_38_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.b LColor.p cert44_seen_38_28_3 = cert44_layer_38_28_3 := by
  decide

theorem cert44_component_38_28_eq :
    closedCollarComponent word (listGetD fiber44 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_38_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 38 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.b LColor.p 27 cert44_seen_38_28_0 = cert44_component_38_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.b LColor.p
    cert44_seen_38_28_0 cert44_layer_38_28_0 26 cert44_layer_38_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.b LColor.p 26 cert44_seen_38_28_1 = cert44_component_38_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.b LColor.p
    cert44_seen_38_28_1 cert44_layer_38_28_1 25 cert44_layer_38_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.b LColor.p 25 cert44_seen_38_28_2 = cert44_component_38_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.b LColor.p
    cert44_seen_38_28_2 cert44_layer_38_28_2 24 cert44_layer_38_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.b LColor.p 24 cert44_seen_38_28_3 = cert44_component_38_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 38 []) LColor.b LColor.p
    cert44_seen_38_28_3 cert44_layer_38_28_3_eq 24

theorem cert44_step_38_28 :
    closedCollarIndexStepBool word fiber44 38 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_38_28)
    (by decide) (by decide)
    (by simpa [cert44_move_38_28] using cert44_component_38_28_eq)
    (by decide) (by decide) (by decide)

def cert44_move_39_29 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_39_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_39_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_39_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_39_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.b LColor.p cert44_seen_39_29_0 = cert44_layer_39_29_0 := by
  decide

def cert44_seen_39_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_39_29_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_39_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.b LColor.p cert44_seen_39_29_1 = cert44_layer_39_29_1 := by
  decide

def cert44_seen_39_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_39_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_39_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.b LColor.p cert44_seen_39_29_2 = cert44_layer_39_29_2 := by
  decide

def cert44_seen_39_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_39_29_3 : List ChainEdge :=
  []

theorem cert44_layer_39_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.b LColor.p cert44_seen_39_29_3 = cert44_layer_39_29_3 := by
  decide

theorem cert44_component_39_29_eq :
    closedCollarComponent word (listGetD fiber44 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_39_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 39 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.b LColor.p 27 cert44_seen_39_29_0 = cert44_component_39_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.b LColor.p
    cert44_seen_39_29_0 cert44_layer_39_29_0 26 cert44_layer_39_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.b LColor.p 26 cert44_seen_39_29_1 = cert44_component_39_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.b LColor.p
    cert44_seen_39_29_1 cert44_layer_39_29_1 25 cert44_layer_39_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.b LColor.p 25 cert44_seen_39_29_2 = cert44_component_39_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.b LColor.p
    cert44_seen_39_29_2 cert44_layer_39_29_2 24 cert44_layer_39_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.b LColor.p 24 cert44_seen_39_29_3 = cert44_component_39_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 39 []) LColor.b LColor.p
    cert44_seen_39_29_3 cert44_layer_39_29_3_eq 24

theorem cert44_step_39_29 :
    closedCollarIndexStepBool word fiber44 39 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_39_29)
    (by decide) (by decide)
    (by simpa [cert44_move_39_29] using cert44_component_39_29_eq)
    (by decide) (by decide) (by decide)

def cert44_move_40_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_40_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_seen_40_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_40_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_40_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.b cert44_seen_40_18_0 = cert44_layer_40_18_0 := by
  decide

def cert44_seen_40_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_40_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_40_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.b cert44_seen_40_18_1 = cert44_layer_40_18_1 := by
  decide

def cert44_seen_40_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_40_18_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_40_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.b cert44_seen_40_18_2 = cert44_layer_40_18_2 := by
  decide

def cert44_seen_40_18_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_40_18_3 : List ChainEdge :=
  []

theorem cert44_layer_40_18_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.b cert44_seen_40_18_3 = cert44_layer_40_18_3 := by
  decide

theorem cert44_component_40_18_eq :
    closedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_40_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 40 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.b 27 cert44_seen_40_18_0 = cert44_component_40_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.b
    cert44_seen_40_18_0 cert44_layer_40_18_0 26 cert44_layer_40_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.b 26 cert44_seen_40_18_1 = cert44_component_40_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.b
    cert44_seen_40_18_1 cert44_layer_40_18_1 25 cert44_layer_40_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.b 25 cert44_seen_40_18_2 = cert44_component_40_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.b
    cert44_seen_40_18_2 cert44_layer_40_18_2 24 cert44_layer_40_18_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.b 24 cert44_seen_40_18_3 = cert44_component_40_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 40 []) LColor.r LColor.b
    cert44_seen_40_18_3 cert44_layer_40_18_3_eq 24

theorem cert44_step_40_18 :
    closedCollarIndexStepBool word fiber44 40 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_40_18)
    (by decide) (by decide)
    (by simpa [cert44_move_40_18] using cert44_component_40_18_eq)
    (by decide) (by decide) (by decide)

def cert44_move_41_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_41_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_seen_41_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_41_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_41_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.b cert44_seen_41_19_0 = cert44_layer_41_19_0 := by
  decide

def cert44_seen_41_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_41_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_41_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.b cert44_seen_41_19_1 = cert44_layer_41_19_1 := by
  decide

def cert44_seen_41_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_41_19_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_41_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.b cert44_seen_41_19_2 = cert44_layer_41_19_2 := by
  decide

def cert44_seen_41_19_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_41_19_3 : List ChainEdge :=
  []

theorem cert44_layer_41_19_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.b cert44_seen_41_19_3 = cert44_layer_41_19_3 := by
  decide

theorem cert44_component_41_19_eq :
    closedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_41_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 41 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.b 27 cert44_seen_41_19_0 = cert44_component_41_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.b
    cert44_seen_41_19_0 cert44_layer_41_19_0 26 cert44_layer_41_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.b 26 cert44_seen_41_19_1 = cert44_component_41_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.b
    cert44_seen_41_19_1 cert44_layer_41_19_1 25 cert44_layer_41_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.b 25 cert44_seen_41_19_2 = cert44_component_41_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.b
    cert44_seen_41_19_2 cert44_layer_41_19_2 24 cert44_layer_41_19_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.b 24 cert44_seen_41_19_3 = cert44_component_41_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 41 []) LColor.r LColor.b
    cert44_seen_41_19_3 cert44_layer_41_19_3_eq 24

theorem cert44_step_41_19 :
    closedCollarIndexStepBool word fiber44 41 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_41_19)
    (by decide) (by decide)
    (by simpa [cert44_move_41_19] using cert44_component_41_19_eq)
    (by decide) (by decide) (by decide)

def cert44_move_42_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_42_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_seen_42_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_42_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_42_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_0 = cert44_layer_42_20_0 := by
  decide

def cert44_seen_42_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_42_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_42_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_1 = cert44_layer_42_20_1 := by
  decide

def cert44_seen_42_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_42_20_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_42_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_2 = cert44_layer_42_20_2 := by
  decide

def cert44_seen_42_20_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_42_20_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_42_20_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_3 = cert44_layer_42_20_3 := by
  decide

def cert44_seen_42_20_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_42_20_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B5 }]

theorem cert44_layer_42_20_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_4 = cert44_layer_42_20_4 := by
  decide

def cert44_seen_42_20_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B5 }]

def cert44_layer_42_20_5 : List ChainEdge :=
  []

theorem cert44_layer_42_20_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.b cert44_seen_42_20_5 = cert44_layer_42_20_5 := by
  decide

theorem cert44_component_42_20_eq :
    closedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_42_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 42 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 27 cert44_seen_42_20_0 = cert44_component_42_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_0 cert44_layer_42_20_0 26 cert44_layer_42_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 26 cert44_seen_42_20_1 = cert44_component_42_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_1 cert44_layer_42_20_1 25 cert44_layer_42_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 25 cert44_seen_42_20_2 = cert44_component_42_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_2 cert44_layer_42_20_2 24 cert44_layer_42_20_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 24 cert44_seen_42_20_3 = cert44_component_42_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_3 cert44_layer_42_20_3 23 cert44_layer_42_20_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 23 cert44_seen_42_20_4 = cert44_component_42_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_4 cert44_layer_42_20_4 22 cert44_layer_42_20_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.b 22 cert44_seen_42_20_5 = cert44_component_42_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 42 []) LColor.r LColor.b
    cert44_seen_42_20_5 cert44_layer_42_20_5_eq 22

theorem cert44_step_42_20 :
    closedCollarIndexStepBool word fiber44 42 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_42_20)
    (by decide) (by decide)
    (by simpa [cert44_move_42_20] using cert44_component_42_20_eq)
    (by decide) (by decide) (by decide)

def cert44_move_43_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_43_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_seen_43_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_43_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_43_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_0 = cert44_layer_43_21_0 := by
  decide

def cert44_seen_43_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_43_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_43_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_1 = cert44_layer_43_21_1 := by
  decide

def cert44_seen_43_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_43_21_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_43_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_2 = cert44_layer_43_21_2 := by
  decide

def cert44_seen_43_21_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_43_21_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

theorem cert44_layer_43_21_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_3 = cert44_layer_43_21_3 := by
  decide

def cert44_seen_43_21_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }]

def cert44_layer_43_21_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B6 }]

theorem cert44_layer_43_21_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_4 = cert44_layer_43_21_4 := by
  decide

def cert44_seen_43_21_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F4F5 }, { occ := 2, edge := TauEdge.F1F0 }, { occ := 1, edge := TauEdge.B6 }]

def cert44_layer_43_21_5 : List ChainEdge :=
  []

theorem cert44_layer_43_21_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.b cert44_seen_43_21_5 = cert44_layer_43_21_5 := by
  decide

theorem cert44_component_43_21_eq :
    closedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = cert44_component_43_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 43 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 27 cert44_seen_43_21_0 = cert44_component_43_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_0 cert44_layer_43_21_0 26 cert44_layer_43_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 26 cert44_seen_43_21_1 = cert44_component_43_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_1 cert44_layer_43_21_1 25 cert44_layer_43_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 25 cert44_seen_43_21_2 = cert44_component_43_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_2 cert44_layer_43_21_2 24 cert44_layer_43_21_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 24 cert44_seen_43_21_3 = cert44_component_43_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_3 cert44_layer_43_21_3 23 cert44_layer_43_21_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 23 cert44_seen_43_21_4 = cert44_component_43_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_4 cert44_layer_43_21_4 22 cert44_layer_43_21_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.b 22 cert44_seen_43_21_5 = cert44_component_43_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 43 []) LColor.r LColor.b
    cert44_seen_43_21_5 cert44_layer_43_21_5_eq 22

theorem cert44_step_43_21 :
    closedCollarIndexStepBool word fiber44 43 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_43_21)
    (by decide) (by decide)
    (by simpa [cert44_move_43_21] using cert44_component_43_21_eq)
    (by decide) (by decide) (by decide)

theorem cert44_row_0 :
    closedCollarParentIndexValid word fiber44 cert44.parents 0 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length]

theorem cert44_row_1 :
    closedCollarParentIndexValid word fiber44 cert44.parents 1 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_1_0, cert44_step_0_1]

theorem cert44_row_2 :
    closedCollarParentIndexValid word fiber44 cert44.parents 2 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_2_1, cert44_step_1_2]

theorem cert44_row_3 :
    closedCollarParentIndexValid word fiber44 cert44.parents 3 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_3_0, cert44_step_0_3]

theorem cert44_row_4 :
    closedCollarParentIndexValid word fiber44 cert44.parents 4 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_4_0, cert44_step_0_4]

theorem cert44_row_5 :
    closedCollarParentIndexValid word fiber44 cert44.parents 5 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_5_1, cert44_step_1_5]

theorem cert44_row_6 :
    closedCollarParentIndexValid word fiber44 cert44.parents 6 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_6_0, cert44_step_0_6]

theorem cert44_row_7 :
    closedCollarParentIndexValid word fiber44 cert44.parents 7 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_7_1, cert44_step_1_7]

theorem cert44_row_8 :
    closedCollarParentIndexValid word fiber44 cert44.parents 8 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_8_2, cert44_step_2_8]

theorem cert44_row_9 :
    closedCollarParentIndexValid word fiber44 cert44.parents 9 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_9_3, cert44_step_3_9]

theorem cert44_row_10 :
    closedCollarParentIndexValid word fiber44 cert44.parents 10 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_10_4, cert44_step_4_10]

theorem cert44_row_11 :
    closedCollarParentIndexValid word fiber44 cert44.parents 11 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_11_5, cert44_step_5_11]

theorem cert44_row_12 :
    closedCollarParentIndexValid word fiber44 cert44.parents 12 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_12_10, cert44_step_10_12]

theorem cert44_row_13 :
    closedCollarParentIndexValid word fiber44 cert44.parents 13 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_13_11, cert44_step_11_13]

theorem cert44_row_14 :
    closedCollarParentIndexValid word fiber44 cert44.parents 14 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_14_6, cert44_step_6_14]

theorem cert44_row_15 :
    closedCollarParentIndexValid word fiber44 cert44.parents 15 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_15_7, cert44_step_7_15]

theorem cert44_row_16 :
    closedCollarParentIndexValid word fiber44 cert44.parents 16 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_16_8, cert44_step_8_16]

theorem cert44_row_17 :
    closedCollarParentIndexValid word fiber44 cert44.parents 17 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_17_9, cert44_step_9_17]

theorem cert44_row_18 :
    closedCollarParentIndexValid word fiber44 cert44.parents 18 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_18_4, cert44_step_4_18]

theorem cert44_row_19 :
    closedCollarParentIndexValid word fiber44 cert44.parents 19 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_19_5, cert44_step_5_19]

theorem cert44_row_20 :
    closedCollarParentIndexValid word fiber44 cert44.parents 20 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_20_0, cert44_step_0_20]

theorem cert44_row_21 :
    closedCollarParentIndexValid word fiber44 cert44.parents 21 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_21_1, cert44_step_1_21]

theorem cert44_row_22 :
    closedCollarParentIndexValid word fiber44 cert44.parents 22 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_22_2, cert44_step_2_22]

theorem cert44_row_23 :
    closedCollarParentIndexValid word fiber44 cert44.parents 23 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_23_3, cert44_step_3_23]

theorem cert44_row_24 :
    closedCollarParentIndexValid word fiber44 cert44.parents 24 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_24_0, cert44_step_0_24]

theorem cert44_row_25 :
    closedCollarParentIndexValid word fiber44 cert44.parents 25 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_25_1, cert44_step_1_25]

theorem cert44_row_26 :
    closedCollarParentIndexValid word fiber44 cert44.parents 26 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_26_2, cert44_step_2_26]

theorem cert44_row_27 :
    closedCollarParentIndexValid word fiber44 cert44.parents 27 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_27_3, cert44_step_3_27]

theorem cert44_row_28 :
    closedCollarParentIndexValid word fiber44 cert44.parents 28 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_28_4, cert44_step_4_28]

theorem cert44_row_29 :
    closedCollarParentIndexValid word fiber44 cert44.parents 29 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_29_5, cert44_step_5_29]

theorem cert44_row_30 :
    closedCollarParentIndexValid word fiber44 cert44.parents 30 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_30_6, cert44_step_6_30]

theorem cert44_row_31 :
    closedCollarParentIndexValid word fiber44 cert44.parents 31 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_31_7, cert44_step_7_31]

theorem cert44_row_32 :
    closedCollarParentIndexValid word fiber44 cert44.parents 32 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_32_8, cert44_step_8_32]

theorem cert44_row_33 :
    closedCollarParentIndexValid word fiber44 cert44.parents 33 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_33_9, cert44_step_9_33]

theorem cert44_row_34 :
    closedCollarParentIndexValid word fiber44 cert44.parents 34 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_34_10, cert44_step_10_34]

theorem cert44_row_35 :
    closedCollarParentIndexValid word fiber44 cert44.parents 35 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_35_11, cert44_step_11_35]

theorem cert44_row_36 :
    closedCollarParentIndexValid word fiber44 cert44.parents 36 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_36_26, cert44_step_26_36]

theorem cert44_row_37 :
    closedCollarParentIndexValid word fiber44 cert44.parents 37 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_37_27, cert44_step_27_37]

theorem cert44_row_38 :
    closedCollarParentIndexValid word fiber44 cert44.parents 38 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_38_28, cert44_step_28_38]

theorem cert44_row_39 :
    closedCollarParentIndexValid word fiber44 cert44.parents 39 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_39_29, cert44_step_29_39]

theorem cert44_row_40 :
    closedCollarParentIndexValid word fiber44 cert44.parents 40 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_40_18, cert44_step_18_40]

theorem cert44_row_41 :
    closedCollarParentIndexValid word fiber44 cert44.parents 41 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_41_19, cert44_step_19_41]

theorem cert44_row_42 :
    closedCollarParentIndexValid word fiber44 cert44.parents 42 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_42_20, cert44_step_20_42]

theorem cert44_row_43 :
    closedCollarParentIndexValid word fiber44 cert44.parents 43 = true := by
  have cert44_fiber_length : fiber44.length = 44 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_43_21, cert44_step_21_43]

theorem cert44_rows :
    closedCollarSpineRowsValid word fiber44 cert44.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert44_fiber_length : fiber44.length = 44 := by decide

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
  by_cases h6 : idx = 6
  · subst idx
    exact cert44_row_6
  by_cases h7 : idx = 7
  · subst idx
    exact cert44_row_7
  by_cases h8 : idx = 8
  · subst idx
    exact cert44_row_8
  by_cases h9 : idx = 9
  · subst idx
    exact cert44_row_9
  by_cases h10 : idx = 10
  · subst idx
    exact cert44_row_10
  by_cases h11 : idx = 11
  · subst idx
    exact cert44_row_11
  by_cases h12 : idx = 12
  · subst idx
    exact cert44_row_12
  by_cases h13 : idx = 13
  · subst idx
    exact cert44_row_13
  by_cases h14 : idx = 14
  · subst idx
    exact cert44_row_14
  by_cases h15 : idx = 15
  · subst idx
    exact cert44_row_15
  by_cases h16 : idx = 16
  · subst idx
    exact cert44_row_16
  by_cases h17 : idx = 17
  · subst idx
    exact cert44_row_17
  by_cases h18 : idx = 18
  · subst idx
    exact cert44_row_18
  by_cases h19 : idx = 19
  · subst idx
    exact cert44_row_19
  by_cases h20 : idx = 20
  · subst idx
    exact cert44_row_20
  by_cases h21 : idx = 21
  · subst idx
    exact cert44_row_21
  by_cases h22 : idx = 22
  · subst idx
    exact cert44_row_22
  by_cases h23 : idx = 23
  · subst idx
    exact cert44_row_23
  by_cases h24 : idx = 24
  · subst idx
    exact cert44_row_24
  by_cases h25 : idx = 25
  · subst idx
    exact cert44_row_25
  by_cases h26 : idx = 26
  · subst idx
    exact cert44_row_26
  by_cases h27 : idx = 27
  · subst idx
    exact cert44_row_27
  by_cases h28 : idx = 28
  · subst idx
    exact cert44_row_28
  by_cases h29 : idx = 29
  · subst idx
    exact cert44_row_29
  by_cases h30 : idx = 30
  · subst idx
    exact cert44_row_30
  by_cases h31 : idx = 31
  · subst idx
    exact cert44_row_31
  by_cases h32 : idx = 32
  · subst idx
    exact cert44_row_32
  by_cases h33 : idx = 33
  · subst idx
    exact cert44_row_33
  by_cases h34 : idx = 34
  · subst idx
    exact cert44_row_34
  by_cases h35 : idx = 35
  · subst idx
    exact cert44_row_35
  by_cases h36 : idx = 36
  · subst idx
    exact cert44_row_36
  by_cases h37 : idx = 37
  · subst idx
    exact cert44_row_37
  by_cases h38 : idx = 38
  · subst idx
    exact cert44_row_38
  by_cases h39 : idx = 39
  · subst idx
    exact cert44_row_39
  by_cases h40 : idx = 40
  · subst idx
    exact cert44_row_40
  by_cases h41 : idx = 41
  · subst idx
    exact cert44_row_41
  by_cases h42 : idx = 42
  · subst idx
    exact cert44_row_42
  by_cases h43 : idx = 43
  · subst idx
    exact cert44_row_43
  · omega

theorem cert44_root :
    closedCollarSpineParentsReachRoot fiber44 cert44 = true := by
  decide

theorem cert44_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert44.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert44 fiber44_eq cert44_rows cert44_root


end GoertzelLemma818ClosedCollarS2Word4
end Mettapedia.GraphTheory.FourColor
