import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

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
, [
  [stateAt 88, stateAt 156, stateAt 148]
, [stateAt 88, stateAt 157, stateAt 156]
, [stateAt 88, stateAt 158, stateAt 48]
, [stateAt 88, stateAt 159, stateAt 56]
, [stateAt 88, stateAt 172, stateAt 132]
, [stateAt 88, stateAt 173, stateAt 140]
, [stateAt 89, stateAt 148, stateAt 148]
, [stateAt 89, stateAt 149, stateAt 156]
, [stateAt 89, stateAt 150, stateAt 48]
, [stateAt 89, stateAt 151, stateAt 56]
, [stateAt 89, stateAt 164, stateAt 132]
, [stateAt 89, stateAt 165, stateAt 140]
, [stateAt 90, stateAt 140, stateAt 148]
, [stateAt 90, stateAt 141, stateAt 156]
, [stateAt 90, stateAt 142, stateAt 48]
, [stateAt 90, stateAt 143, stateAt 56]
, [stateAt 90, stateAt 188, stateAt 132]
, [stateAt 90, stateAt 189, stateAt 140]
, [stateAt 91, stateAt 132, stateAt 148]
, [stateAt 91, stateAt 133, stateAt 156]
, [stateAt 91, stateAt 134, stateAt 48]
, [stateAt 91, stateAt 135, stateAt 56]
, [stateAt 91, stateAt 180, stateAt 132]
, [stateAt 91, stateAt 181, stateAt 140]
]
, [
  [stateAt 108, stateAt 26, stateAt 32]
, [stateAt 108, stateAt 27, stateAt 40]
, [stateAt 108, stateAt 40, stateAt 148]
, [stateAt 108, stateAt 41, stateAt 156]
, [stateAt 108, stateAt 42, stateAt 48]
, [stateAt 108, stateAt 43, stateAt 56]
, [stateAt 109, stateAt 18, stateAt 32]
, [stateAt 109, stateAt 19, stateAt 40]
, [stateAt 109, stateAt 32, stateAt 148]
, [stateAt 109, stateAt 33, stateAt 156]
, [stateAt 109, stateAt 34, stateAt 48]
, [stateAt 109, stateAt 35, stateAt 56]
, [stateAt 110, stateAt 10, stateAt 32]
, [stateAt 110, stateAt 11, stateAt 40]
, [stateAt 110, stateAt 56, stateAt 148]
, [stateAt 110, stateAt 57, stateAt 156]
, [stateAt 110, stateAt 58, stateAt 48]
, [stateAt 110, stateAt 59, stateAt 56]
, [stateAt 111, stateAt 2, stateAt 32]
, [stateAt 111, stateAt 3, stateAt 40]
, [stateAt 111, stateAt 48, stateAt 148]
, [stateAt 111, stateAt 49, stateAt 156]
, [stateAt 111, stateAt 50, stateAt 48]
, [stateAt 111, stateAt 51, stateAt 56]
]
, []
, []
, []
, []
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
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.b, LColor.b, LColor.p, LColor.p]
  exact hfast.trans fiber44_keyed_eq

def cert44 : ClosedCollarSpineCertificate :=
  { key := [LColor.b, LColor.b, LColor.p, LColor.p],
    root := 0,
    maxDepth := 4,
    parents := [0, 0, 1, 0, 0, 1, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 12, 13, 14, 15, 42, 43, 44, 45, 46, 47, 10, 11, 6, 7, 8, 9, 4, 5, 0, 1, 2, 3] }

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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_0_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_0_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_0_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_6_0 = cert44_layer_0_6_0 := by
  decide

def cert44_seen_0_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_0_6_1 : List ChainEdge :=
  []

theorem cert44_layer_0_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.b LColor.p cert44_seen_0_6_1 = cert44_layer_0_6_1 := by
  decide

theorem cert44_component_0_6_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_0_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_0_12 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_0_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_0_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_0_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_12_0 = cert44_layer_0_12_0 := by
  decide

def cert44_seen_0_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_0_12_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_0_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_12_1 = cert44_layer_0_12_1 := by
  decide

def cert44_seen_0_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_0_12_2 : List ChainEdge :=
  []

theorem cert44_layer_0_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.b cert44_seen_0_12_2 = cert44_layer_0_12_2 := by
  decide

theorem cert44_component_0_12_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_0_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 27 cert44_seen_0_12_0 = cert44_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_12_0 cert44_layer_0_12_0 26 cert44_layer_0_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 26 cert44_seen_0_12_1 = cert44_component_0_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_12_1 cert44_layer_0_12_1 25 cert44_layer_0_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.b 25 cert44_seen_0_12_2 = cert44_component_0_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.b
    cert44_seen_0_12_2 cert44_layer_0_12_2_eq 25

theorem cert44_step_0_12 :
    closedCollarIndexStepBool word fiber44 0 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_12)
    (by decide) (by decide)
    (by simpa [cert44_move_0_12] using cert44_component_0_12_eq)
    (by decide) (by decide) (by decide)

def cert44_move_0_44 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_0_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_0_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_0_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_0_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_44_0 = cert44_layer_0_44_0 := by
  decide

def cert44_seen_0_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_0_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_0_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_44_1 = cert44_layer_0_44_1 := by
  decide

def cert44_seen_0_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_0_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_0_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_44_2 = cert44_layer_0_44_2 := by
  decide

def cert44_seen_0_44_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_0_44_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_0_44_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_44_3 = cert44_layer_0_44_3 := by
  decide

def cert44_seen_0_44_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_0_44_4 : List ChainEdge :=
  []

theorem cert44_layer_0_44_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 0 [])
      LColor.r LColor.p cert44_seen_0_44_4 = cert44_layer_0_44_4 := by
  decide

theorem cert44_component_0_44_eq :
    closedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_0_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 0 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 27 cert44_seen_0_44_0 = cert44_component_0_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_44_0 cert44_layer_0_44_0 26 cert44_layer_0_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 26 cert44_seen_0_44_1 = cert44_component_0_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_44_1 cert44_layer_0_44_1 25 cert44_layer_0_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 25 cert44_seen_0_44_2 = cert44_component_0_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_44_2 cert44_layer_0_44_2 24 cert44_layer_0_44_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 24 cert44_seen_0_44_3 = cert44_component_0_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_44_3 cert44_layer_0_44_3 23 cert44_layer_0_44_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 0 [])
      LColor.r LColor.p 23 cert44_seen_0_44_4 = cert44_component_0_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 0 []) LColor.r LColor.p
    cert44_seen_0_44_4 cert44_layer_0_44_4_eq 23

theorem cert44_step_0_44 :
    closedCollarIndexStepBool word fiber44 0 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_0_44)
    (by decide) (by decide)
    (by simpa [cert44_move_0_44] using cert44_component_0_44_eq)
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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_1_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_1_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_1_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_7_0 = cert44_layer_1_7_0 := by
  decide

def cert44_seen_1_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_1_7_1 : List ChainEdge :=
  []

theorem cert44_layer_1_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.b LColor.p cert44_seen_1_7_1 = cert44_layer_1_7_1 := by
  decide

theorem cert44_component_1_7_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_1_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_1_13 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_1_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_1_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_1_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_13_0 = cert44_layer_1_13_0 := by
  decide

def cert44_seen_1_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_1_13_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_1_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_13_1 = cert44_layer_1_13_1 := by
  decide

def cert44_seen_1_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_1_13_2 : List ChainEdge :=
  []

theorem cert44_layer_1_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.b cert44_seen_1_13_2 = cert44_layer_1_13_2 := by
  decide

theorem cert44_component_1_13_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_1_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 27 cert44_seen_1_13_0 = cert44_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_13_0 cert44_layer_1_13_0 26 cert44_layer_1_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 26 cert44_seen_1_13_1 = cert44_component_1_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_13_1 cert44_layer_1_13_1 25 cert44_layer_1_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.b 25 cert44_seen_1_13_2 = cert44_component_1_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.b
    cert44_seen_1_13_2 cert44_layer_1_13_2_eq 25

theorem cert44_step_1_13 :
    closedCollarIndexStepBool word fiber44 1 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_13)
    (by decide) (by decide)
    (by simpa [cert44_move_1_13] using cert44_component_1_13_eq)
    (by decide) (by decide) (by decide)

def cert44_move_1_45 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_1_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_1_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_1_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_1_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_45_0 = cert44_layer_1_45_0 := by
  decide

def cert44_seen_1_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_1_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_1_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_45_1 = cert44_layer_1_45_1 := by
  decide

def cert44_seen_1_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_1_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_1_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_45_2 = cert44_layer_1_45_2 := by
  decide

def cert44_seen_1_45_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_1_45_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_1_45_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_45_3 = cert44_layer_1_45_3 := by
  decide

def cert44_seen_1_45_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_1_45_4 : List ChainEdge :=
  []

theorem cert44_layer_1_45_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 1 [])
      LColor.r LColor.p cert44_seen_1_45_4 = cert44_layer_1_45_4 := by
  decide

theorem cert44_component_1_45_eq :
    closedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_1_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 1 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 27 cert44_seen_1_45_0 = cert44_component_1_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_45_0 cert44_layer_1_45_0 26 cert44_layer_1_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 26 cert44_seen_1_45_1 = cert44_component_1_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_45_1 cert44_layer_1_45_1 25 cert44_layer_1_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 25 cert44_seen_1_45_2 = cert44_component_1_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_45_2 cert44_layer_1_45_2 24 cert44_layer_1_45_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 24 cert44_seen_1_45_3 = cert44_component_1_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_45_3 cert44_layer_1_45_3 23 cert44_layer_1_45_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 1 [])
      LColor.r LColor.p 23 cert44_seen_1_45_4 = cert44_component_1_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 1 []) LColor.r LColor.p
    cert44_seen_1_45_4 cert44_layer_1_45_4_eq 23

theorem cert44_step_1_45 :
    closedCollarIndexStepBool word fiber44 1 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_1_45)
    (by decide) (by decide)
    (by simpa [cert44_move_1_45] using cert44_component_1_45_eq)
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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_2_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_2_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_2_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.b LColor.p cert44_seen_2_8_0 = cert44_layer_2_8_0 := by
  decide

def cert44_seen_2_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_2_8_1 : List ChainEdge :=
  []

theorem cert44_layer_2_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.b LColor.p cert44_seen_2_8_1 = cert44_layer_2_8_1 := by
  decide

theorem cert44_component_2_8_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_2_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_2_14 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_2_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_2_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_2_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_14_0 = cert44_layer_2_14_0 := by
  decide

def cert44_seen_2_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_2_14_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_2_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_14_1 = cert44_layer_2_14_1 := by
  decide

def cert44_seen_2_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_2_14_2 : List ChainEdge :=
  []

theorem cert44_layer_2_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.b cert44_seen_2_14_2 = cert44_layer_2_14_2 := by
  decide

theorem cert44_component_2_14_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_2_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 27 cert44_seen_2_14_0 = cert44_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_14_0 cert44_layer_2_14_0 26 cert44_layer_2_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 26 cert44_seen_2_14_1 = cert44_component_2_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_14_1 cert44_layer_2_14_1 25 cert44_layer_2_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.b 25 cert44_seen_2_14_2 = cert44_component_2_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.b
    cert44_seen_2_14_2 cert44_layer_2_14_2_eq 25

theorem cert44_step_2_14 :
    closedCollarIndexStepBool word fiber44 2 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_14)
    (by decide) (by decide)
    (by simpa [cert44_move_2_14] using cert44_component_2_14_eq)
    (by decide) (by decide) (by decide)

def cert44_move_2_46 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_2_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_2_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_2_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_2_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_46_0 = cert44_layer_2_46_0 := by
  decide

def cert44_seen_2_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_2_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_2_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_46_1 = cert44_layer_2_46_1 := by
  decide

def cert44_seen_2_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_2_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_2_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_46_2 = cert44_layer_2_46_2 := by
  decide

def cert44_seen_2_46_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_2_46_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_2_46_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_46_3 = cert44_layer_2_46_3 := by
  decide

def cert44_seen_2_46_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_2_46_4 : List ChainEdge :=
  []

theorem cert44_layer_2_46_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 2 [])
      LColor.r LColor.p cert44_seen_2_46_4 = cert44_layer_2_46_4 := by
  decide

theorem cert44_component_2_46_eq :
    closedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_2_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 2 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 27 cert44_seen_2_46_0 = cert44_component_2_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_46_0 cert44_layer_2_46_0 26 cert44_layer_2_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 26 cert44_seen_2_46_1 = cert44_component_2_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_46_1 cert44_layer_2_46_1 25 cert44_layer_2_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 25 cert44_seen_2_46_2 = cert44_component_2_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_46_2 cert44_layer_2_46_2 24 cert44_layer_2_46_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 24 cert44_seen_2_46_3 = cert44_component_2_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_46_3 cert44_layer_2_46_3 23 cert44_layer_2_46_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 2 [])
      LColor.r LColor.p 23 cert44_seen_2_46_4 = cert44_component_2_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 2 []) LColor.r LColor.p
    cert44_seen_2_46_4 cert44_layer_2_46_4_eq 23

theorem cert44_step_2_46 :
    closedCollarIndexStepBool word fiber44 2 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_2_46)
    (by decide) (by decide)
    (by simpa [cert44_move_2_46] using cert44_component_2_46_eq)
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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_3_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_3_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_3_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.b LColor.p cert44_seen_3_9_0 = cert44_layer_3_9_0 := by
  decide

def cert44_seen_3_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_3_9_1 : List ChainEdge :=
  []

theorem cert44_layer_3_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.b LColor.p cert44_seen_3_9_1 = cert44_layer_3_9_1 := by
  decide

theorem cert44_component_3_9_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_3_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_3_15 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_3_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_3_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_3_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_15_0 = cert44_layer_3_15_0 := by
  decide

def cert44_seen_3_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_3_15_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_3_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_15_1 = cert44_layer_3_15_1 := by
  decide

def cert44_seen_3_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_3_15_2 : List ChainEdge :=
  []

theorem cert44_layer_3_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.b cert44_seen_3_15_2 = cert44_layer_3_15_2 := by
  decide

theorem cert44_component_3_15_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_3_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 27 cert44_seen_3_15_0 = cert44_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_15_0 cert44_layer_3_15_0 26 cert44_layer_3_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 26 cert44_seen_3_15_1 = cert44_component_3_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_15_1 cert44_layer_3_15_1 25 cert44_layer_3_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.b 25 cert44_seen_3_15_2 = cert44_component_3_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.b
    cert44_seen_3_15_2 cert44_layer_3_15_2_eq 25

theorem cert44_step_3_15 :
    closedCollarIndexStepBool word fiber44 3 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_15)
    (by decide) (by decide)
    (by simpa [cert44_move_3_15] using cert44_component_3_15_eq)
    (by decide) (by decide) (by decide)

def cert44_move_3_47 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_3_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_3_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_3_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_3_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_47_0 = cert44_layer_3_47_0 := by
  decide

def cert44_seen_3_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_3_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_3_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_47_1 = cert44_layer_3_47_1 := by
  decide

def cert44_seen_3_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_3_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_3_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_47_2 = cert44_layer_3_47_2 := by
  decide

def cert44_seen_3_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_3_47_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_3_47_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_47_3 = cert44_layer_3_47_3 := by
  decide

def cert44_seen_3_47_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_3_47_4 : List ChainEdge :=
  []

theorem cert44_layer_3_47_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 3 [])
      LColor.r LColor.p cert44_seen_3_47_4 = cert44_layer_3_47_4 := by
  decide

theorem cert44_component_3_47_eq :
    closedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_3_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 3 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 27 cert44_seen_3_47_0 = cert44_component_3_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_47_0 cert44_layer_3_47_0 26 cert44_layer_3_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 26 cert44_seen_3_47_1 = cert44_component_3_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_47_1 cert44_layer_3_47_1 25 cert44_layer_3_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 25 cert44_seen_3_47_2 = cert44_component_3_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_47_2 cert44_layer_3_47_2 24 cert44_layer_3_47_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 24 cert44_seen_3_47_3 = cert44_component_3_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_47_3 cert44_layer_3_47_3 23 cert44_layer_3_47_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 3 [])
      LColor.r LColor.p 23 cert44_seen_3_47_4 = cert44_component_3_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 3 []) LColor.r LColor.p
    cert44_seen_3_47_4 cert44_layer_3_47_4_eq 23

theorem cert44_step_3_47 :
    closedCollarIndexStepBool word fiber44 3 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_3_47)
    (by decide) (by decide)
    (by simpa [cert44_move_3_47] using cert44_component_3_47_eq)
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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_4_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_4_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_4_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.b LColor.p cert44_seen_4_10_0 = cert44_layer_4_10_0 := by
  decide

def cert44_seen_4_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_4_10_1 : List ChainEdge :=
  []

theorem cert44_layer_4_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.b LColor.p cert44_seen_4_10_1 = cert44_layer_4_10_1 := by
  decide

theorem cert44_component_4_10_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_4_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_4_16 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_4_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_4_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_4_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_16_0 = cert44_layer_4_16_0 := by
  decide

def cert44_seen_4_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_4_16_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_4_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_16_1 = cert44_layer_4_16_1 := by
  decide

def cert44_seen_4_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_4_16_2 : List ChainEdge :=
  []

theorem cert44_layer_4_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.b cert44_seen_4_16_2 = cert44_layer_4_16_2 := by
  decide

theorem cert44_component_4_16_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_4_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 27 cert44_seen_4_16_0 = cert44_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_16_0 cert44_layer_4_16_0 26 cert44_layer_4_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 26 cert44_seen_4_16_1 = cert44_component_4_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_16_1 cert44_layer_4_16_1 25 cert44_layer_4_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.b 25 cert44_seen_4_16_2 = cert44_component_4_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.b
    cert44_seen_4_16_2 cert44_layer_4_16_2_eq 25

theorem cert44_step_4_16 :
    closedCollarIndexStepBool word fiber44 4 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_16)
    (by decide) (by decide)
    (by simpa [cert44_move_4_16] using cert44_component_4_16_eq)
    (by decide) (by decide) (by decide)

def cert44_move_4_42 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_4_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_4_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_4_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_4_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_0 = cert44_layer_4_42_0 := by
  decide

def cert44_seen_4_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_4_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_4_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_1 = cert44_layer_4_42_1 := by
  decide

def cert44_seen_4_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_4_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_4_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_2 = cert44_layer_4_42_2 := by
  decide

def cert44_seen_4_42_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_4_42_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_4_42_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_3 = cert44_layer_4_42_3 := by
  decide

def cert44_seen_4_42_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_4_42_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_4_42_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_4 = cert44_layer_4_42_4 := by
  decide

def cert44_seen_4_42_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_4_42_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_4_42_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_5 = cert44_layer_4_42_5 := by
  decide

def cert44_seen_4_42_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_4_42_6 : List ChainEdge :=
  []

theorem cert44_layer_4_42_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 4 [])
      LColor.r LColor.p cert44_seen_4_42_6 = cert44_layer_4_42_6 := by
  decide

theorem cert44_component_4_42_eq :
    closedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_4_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 4 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 27 cert44_seen_4_42_0 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_0 cert44_layer_4_42_0 26 cert44_layer_4_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 26 cert44_seen_4_42_1 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_1 cert44_layer_4_42_1 25 cert44_layer_4_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 25 cert44_seen_4_42_2 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_2 cert44_layer_4_42_2 24 cert44_layer_4_42_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 24 cert44_seen_4_42_3 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_3 cert44_layer_4_42_3 23 cert44_layer_4_42_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 23 cert44_seen_4_42_4 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_4 cert44_layer_4_42_4 22 cert44_layer_4_42_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 22 cert44_seen_4_42_5 = cert44_component_4_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_5 cert44_layer_4_42_5 21 cert44_layer_4_42_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 4 [])
      LColor.r LColor.p 21 cert44_seen_4_42_6 = cert44_component_4_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 4 []) LColor.r LColor.p
    cert44_seen_4_42_6 cert44_layer_4_42_6_eq 21

theorem cert44_step_4_42 :
    closedCollarIndexStepBool word fiber44 4 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_4_42)
    (by decide) (by decide)
    (by simpa [cert44_move_4_42] using cert44_component_4_42_eq)
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
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_5_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_5_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_5_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.b LColor.p cert44_seen_5_11_0 = cert44_layer_5_11_0 := by
  decide

def cert44_seen_5_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_5_11_1 : List ChainEdge :=
  []

theorem cert44_layer_5_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.b LColor.p cert44_seen_5_11_1 = cert44_layer_5_11_1 := by
  decide

theorem cert44_component_5_11_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_5_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_5_17 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_5_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_5_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_5_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_17_0 = cert44_layer_5_17_0 := by
  decide

def cert44_seen_5_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_5_17_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_5_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_17_1 = cert44_layer_5_17_1 := by
  decide

def cert44_seen_5_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_5_17_2 : List ChainEdge :=
  []

theorem cert44_layer_5_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.b cert44_seen_5_17_2 = cert44_layer_5_17_2 := by
  decide

theorem cert44_component_5_17_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_5_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 27 cert44_seen_5_17_0 = cert44_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_17_0 cert44_layer_5_17_0 26 cert44_layer_5_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 26 cert44_seen_5_17_1 = cert44_component_5_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_17_1 cert44_layer_5_17_1 25 cert44_layer_5_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.b 25 cert44_seen_5_17_2 = cert44_component_5_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.b
    cert44_seen_5_17_2 cert44_layer_5_17_2_eq 25

theorem cert44_step_5_17 :
    closedCollarIndexStepBool word fiber44 5 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_17)
    (by decide) (by decide)
    (by simpa [cert44_move_5_17] using cert44_component_5_17_eq)
    (by decide) (by decide) (by decide)

def cert44_move_5_43 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_5_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_5_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_5_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_5_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_0 = cert44_layer_5_43_0 := by
  decide

def cert44_seen_5_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_5_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_5_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_1 = cert44_layer_5_43_1 := by
  decide

def cert44_seen_5_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_5_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_5_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_2 = cert44_layer_5_43_2 := by
  decide

def cert44_seen_5_43_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_5_43_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_5_43_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_3 = cert44_layer_5_43_3 := by
  decide

def cert44_seen_5_43_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_5_43_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_5_43_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_4 = cert44_layer_5_43_4 := by
  decide

def cert44_seen_5_43_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_5_43_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_5_43_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_5 = cert44_layer_5_43_5 := by
  decide

def cert44_seen_5_43_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_5_43_6 : List ChainEdge :=
  []

theorem cert44_layer_5_43_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 5 [])
      LColor.r LColor.p cert44_seen_5_43_6 = cert44_layer_5_43_6 := by
  decide

theorem cert44_component_5_43_eq :
    closedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_5_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 5 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 27 cert44_seen_5_43_0 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_0 cert44_layer_5_43_0 26 cert44_layer_5_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 26 cert44_seen_5_43_1 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_1 cert44_layer_5_43_1 25 cert44_layer_5_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 25 cert44_seen_5_43_2 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_2 cert44_layer_5_43_2 24 cert44_layer_5_43_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 24 cert44_seen_5_43_3 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_3 cert44_layer_5_43_3 23 cert44_layer_5_43_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 23 cert44_seen_5_43_4 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_4 cert44_layer_5_43_4 22 cert44_layer_5_43_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 22 cert44_seen_5_43_5 = cert44_component_5_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_5 cert44_layer_5_43_5 21 cert44_layer_5_43_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 5 [])
      LColor.r LColor.p 21 cert44_seen_5_43_6 = cert44_component_5_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 5 []) LColor.r LColor.p
    cert44_seen_5_43_6 cert44_layer_5_43_6_eq 21

theorem cert44_step_5_43 :
    closedCollarIndexStepBool word fiber44 5 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_5_43)
    (by decide) (by decide)
    (by simpa [cert44_move_5_43] using cert44_component_5_43_eq)
    (by decide) (by decide) (by decide)

def cert44_move_6_0 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_6_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_6_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.b LColor.p cert44_seen_6_0_0 = cert44_layer_6_0_0 := by
  decide

def cert44_seen_6_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_6_0_1 : List ChainEdge :=
  []

theorem cert44_layer_6_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.b LColor.p cert44_seen_6_0_1 = cert44_layer_6_0_1 := by
  decide

theorem cert44_component_6_0_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_6_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_6_18 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_6_18 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_6_18_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_6_18_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_18_0 = cert44_layer_6_18_0 := by
  decide

def cert44_seen_6_18_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_6_18_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_6_18_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_18_1 = cert44_layer_6_18_1 := by
  decide

def cert44_seen_6_18_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_6_18_2 : List ChainEdge :=
  []

theorem cert44_layer_6_18_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.b cert44_seen_6_18_2 = cert44_layer_6_18_2 := by
  decide

theorem cert44_component_6_18_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_6_18 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 27 cert44_seen_6_18_0 = cert44_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_18_0 cert44_layer_6_18_0 26 cert44_layer_6_18_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 26 cert44_seen_6_18_1 = cert44_component_6_18
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_18_1 cert44_layer_6_18_1 25 cert44_layer_6_18_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.b 25 cert44_seen_6_18_2 = cert44_component_6_18
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 6 []) LColor.r LColor.b
    cert44_seen_6_18_2 cert44_layer_6_18_2_eq 25

theorem cert44_step_6_18 :
    closedCollarIndexStepBool word fiber44 6 18 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_6_18)
    (by decide) (by decide)
    (by simpa [cert44_move_6_18] using cert44_component_6_18_eq)
    (by decide) (by decide) (by decide)

def cert44_move_6_38 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_6_38 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_6_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_6_38_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_6_38_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_38_0 = cert44_layer_6_38_0 := by
  decide

def cert44_seen_6_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_6_38_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_6_38_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_38_1 = cert44_layer_6_38_1 := by
  decide

def cert44_seen_6_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_6_38_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_6_38_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_38_2 = cert44_layer_6_38_2 := by
  decide

def cert44_seen_6_38_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_6_38_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_6_38_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_38_3 = cert44_layer_6_38_3 := by
  decide

def cert44_seen_6_38_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_6_38_4 : List ChainEdge :=
  []

theorem cert44_layer_6_38_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 6 [])
      LColor.r LColor.p cert44_seen_6_38_4 = cert44_layer_6_38_4 := by
  decide

theorem cert44_component_6_38_eq :
    closedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_6_38 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 6 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 27 cert44_seen_6_38_0 = cert44_component_6_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_38_0 cert44_layer_6_38_0 26 cert44_layer_6_38_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 26 cert44_seen_6_38_1 = cert44_component_6_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_38_1 cert44_layer_6_38_1 25 cert44_layer_6_38_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 25 cert44_seen_6_38_2 = cert44_component_6_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_38_2 cert44_layer_6_38_2 24 cert44_layer_6_38_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 24 cert44_seen_6_38_3 = cert44_component_6_38
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_38_3 cert44_layer_6_38_3 23 cert44_layer_6_38_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 6 [])
      LColor.r LColor.p 23 cert44_seen_6_38_4 = cert44_component_6_38
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 6 []) LColor.r LColor.p
    cert44_seen_6_38_4 cert44_layer_6_38_4_eq 23

theorem cert44_step_6_38 :
    closedCollarIndexStepBool word fiber44 6 38 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_6_38)
    (by decide) (by decide)
    (by simpa [cert44_move_6_38] using cert44_component_6_38_eq)
    (by decide) (by decide) (by decide)

def cert44_move_7_1 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_7_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_7_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.b LColor.p cert44_seen_7_1_0 = cert44_layer_7_1_0 := by
  decide

def cert44_seen_7_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_7_1_1 : List ChainEdge :=
  []

theorem cert44_layer_7_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.b LColor.p cert44_seen_7_1_1 = cert44_layer_7_1_1 := by
  decide

theorem cert44_component_7_1_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_7_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_7_19 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_7_19 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_7_19_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_7_19_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_19_0 = cert44_layer_7_19_0 := by
  decide

def cert44_seen_7_19_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_7_19_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_7_19_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_19_1 = cert44_layer_7_19_1 := by
  decide

def cert44_seen_7_19_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_7_19_2 : List ChainEdge :=
  []

theorem cert44_layer_7_19_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.b cert44_seen_7_19_2 = cert44_layer_7_19_2 := by
  decide

theorem cert44_component_7_19_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_7_19 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 27 cert44_seen_7_19_0 = cert44_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_19_0 cert44_layer_7_19_0 26 cert44_layer_7_19_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 26 cert44_seen_7_19_1 = cert44_component_7_19
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_19_1 cert44_layer_7_19_1 25 cert44_layer_7_19_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.b 25 cert44_seen_7_19_2 = cert44_component_7_19
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 7 []) LColor.r LColor.b
    cert44_seen_7_19_2 cert44_layer_7_19_2_eq 25

theorem cert44_step_7_19 :
    closedCollarIndexStepBool word fiber44 7 19 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_7_19)
    (by decide) (by decide)
    (by simpa [cert44_move_7_19] using cert44_component_7_19_eq)
    (by decide) (by decide) (by decide)

def cert44_move_7_39 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_7_39 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_7_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_7_39_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_7_39_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_39_0 = cert44_layer_7_39_0 := by
  decide

def cert44_seen_7_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_7_39_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_7_39_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_39_1 = cert44_layer_7_39_1 := by
  decide

def cert44_seen_7_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_7_39_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_7_39_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_39_2 = cert44_layer_7_39_2 := by
  decide

def cert44_seen_7_39_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_7_39_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_7_39_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_39_3 = cert44_layer_7_39_3 := by
  decide

def cert44_seen_7_39_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_7_39_4 : List ChainEdge :=
  []

theorem cert44_layer_7_39_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 7 [])
      LColor.r LColor.p cert44_seen_7_39_4 = cert44_layer_7_39_4 := by
  decide

theorem cert44_component_7_39_eq :
    closedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_7_39 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 7 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 27 cert44_seen_7_39_0 = cert44_component_7_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_39_0 cert44_layer_7_39_0 26 cert44_layer_7_39_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 26 cert44_seen_7_39_1 = cert44_component_7_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_39_1 cert44_layer_7_39_1 25 cert44_layer_7_39_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 25 cert44_seen_7_39_2 = cert44_component_7_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_39_2 cert44_layer_7_39_2 24 cert44_layer_7_39_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 24 cert44_seen_7_39_3 = cert44_component_7_39
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_39_3 cert44_layer_7_39_3 23 cert44_layer_7_39_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 7 [])
      LColor.r LColor.p 23 cert44_seen_7_39_4 = cert44_component_7_39
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 7 []) LColor.r LColor.p
    cert44_seen_7_39_4 cert44_layer_7_39_4_eq 23

theorem cert44_step_7_39 :
    closedCollarIndexStepBool word fiber44 7 39 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_7_39)
    (by decide) (by decide)
    (by simpa [cert44_move_7_39] using cert44_component_7_39_eq)
    (by decide) (by decide) (by decide)

def cert44_move_8_2 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_8_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_8_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.b LColor.p cert44_seen_8_2_0 = cert44_layer_8_2_0 := by
  decide

def cert44_seen_8_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_8_2_1 : List ChainEdge :=
  []

theorem cert44_layer_8_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.b LColor.p cert44_seen_8_2_1 = cert44_layer_8_2_1 := by
  decide

theorem cert44_component_8_2_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_8_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_8_20 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_8_20 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_8_20_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_8_20_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_20_0 = cert44_layer_8_20_0 := by
  decide

def cert44_seen_8_20_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_8_20_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_8_20_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_20_1 = cert44_layer_8_20_1 := by
  decide

def cert44_seen_8_20_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_8_20_2 : List ChainEdge :=
  []

theorem cert44_layer_8_20_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.b cert44_seen_8_20_2 = cert44_layer_8_20_2 := by
  decide

theorem cert44_component_8_20_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_8_20 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 27 cert44_seen_8_20_0 = cert44_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_20_0 cert44_layer_8_20_0 26 cert44_layer_8_20_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 26 cert44_seen_8_20_1 = cert44_component_8_20
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_20_1 cert44_layer_8_20_1 25 cert44_layer_8_20_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.b 25 cert44_seen_8_20_2 = cert44_component_8_20
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 8 []) LColor.r LColor.b
    cert44_seen_8_20_2 cert44_layer_8_20_2_eq 25

theorem cert44_step_8_20 :
    closedCollarIndexStepBool word fiber44 8 20 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_8_20)
    (by decide) (by decide)
    (by simpa [cert44_move_8_20] using cert44_component_8_20_eq)
    (by decide) (by decide) (by decide)

def cert44_move_8_40 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_8_40 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_8_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_8_40_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_8_40_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_40_0 = cert44_layer_8_40_0 := by
  decide

def cert44_seen_8_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_8_40_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_8_40_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_40_1 = cert44_layer_8_40_1 := by
  decide

def cert44_seen_8_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_8_40_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_8_40_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_40_2 = cert44_layer_8_40_2 := by
  decide

def cert44_seen_8_40_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_8_40_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_8_40_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_40_3 = cert44_layer_8_40_3 := by
  decide

def cert44_seen_8_40_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_8_40_4 : List ChainEdge :=
  []

theorem cert44_layer_8_40_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 8 [])
      LColor.r LColor.p cert44_seen_8_40_4 = cert44_layer_8_40_4 := by
  decide

theorem cert44_component_8_40_eq :
    closedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_8_40 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 8 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 27 cert44_seen_8_40_0 = cert44_component_8_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_40_0 cert44_layer_8_40_0 26 cert44_layer_8_40_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 26 cert44_seen_8_40_1 = cert44_component_8_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_40_1 cert44_layer_8_40_1 25 cert44_layer_8_40_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 25 cert44_seen_8_40_2 = cert44_component_8_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_40_2 cert44_layer_8_40_2 24 cert44_layer_8_40_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 24 cert44_seen_8_40_3 = cert44_component_8_40
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_40_3 cert44_layer_8_40_3 23 cert44_layer_8_40_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 8 [])
      LColor.r LColor.p 23 cert44_seen_8_40_4 = cert44_component_8_40
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 8 []) LColor.r LColor.p
    cert44_seen_8_40_4 cert44_layer_8_40_4_eq 23

theorem cert44_step_8_40 :
    closedCollarIndexStepBool word fiber44 8 40 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_8_40)
    (by decide) (by decide)
    (by simpa [cert44_move_8_40] using cert44_component_8_40_eq)
    (by decide) (by decide) (by decide)

def cert44_move_9_3 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_9_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_9_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.b LColor.p cert44_seen_9_3_0 = cert44_layer_9_3_0 := by
  decide

def cert44_seen_9_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_9_3_1 : List ChainEdge :=
  []

theorem cert44_layer_9_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.b LColor.p cert44_seen_9_3_1 = cert44_layer_9_3_1 := by
  decide

theorem cert44_component_9_3_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_9_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_9_21 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_9_21 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_9_21_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_9_21_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_21_0 = cert44_layer_9_21_0 := by
  decide

def cert44_seen_9_21_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_9_21_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_9_21_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_21_1 = cert44_layer_9_21_1 := by
  decide

def cert44_seen_9_21_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_9_21_2 : List ChainEdge :=
  []

theorem cert44_layer_9_21_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.b cert44_seen_9_21_2 = cert44_layer_9_21_2 := by
  decide

theorem cert44_component_9_21_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_9_21 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 27 cert44_seen_9_21_0 = cert44_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_21_0 cert44_layer_9_21_0 26 cert44_layer_9_21_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 26 cert44_seen_9_21_1 = cert44_component_9_21
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_21_1 cert44_layer_9_21_1 25 cert44_layer_9_21_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.b 25 cert44_seen_9_21_2 = cert44_component_9_21
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 9 []) LColor.r LColor.b
    cert44_seen_9_21_2 cert44_layer_9_21_2_eq 25

theorem cert44_step_9_21 :
    closedCollarIndexStepBool word fiber44 9 21 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_9_21)
    (by decide) (by decide)
    (by simpa [cert44_move_9_21] using cert44_component_9_21_eq)
    (by decide) (by decide) (by decide)

def cert44_move_9_41 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_9_41 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_9_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_9_41_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_9_41_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_41_0 = cert44_layer_9_41_0 := by
  decide

def cert44_seen_9_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_9_41_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_9_41_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_41_1 = cert44_layer_9_41_1 := by
  decide

def cert44_seen_9_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_9_41_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_9_41_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_41_2 = cert44_layer_9_41_2 := by
  decide

def cert44_seen_9_41_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_9_41_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_9_41_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_41_3 = cert44_layer_9_41_3 := by
  decide

def cert44_seen_9_41_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_9_41_4 : List ChainEdge :=
  []

theorem cert44_layer_9_41_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 9 [])
      LColor.r LColor.p cert44_seen_9_41_4 = cert44_layer_9_41_4 := by
  decide

theorem cert44_component_9_41_eq :
    closedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_9_41 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 9 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 27 cert44_seen_9_41_0 = cert44_component_9_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_41_0 cert44_layer_9_41_0 26 cert44_layer_9_41_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 26 cert44_seen_9_41_1 = cert44_component_9_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_41_1 cert44_layer_9_41_1 25 cert44_layer_9_41_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 25 cert44_seen_9_41_2 = cert44_component_9_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_41_2 cert44_layer_9_41_2 24 cert44_layer_9_41_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 24 cert44_seen_9_41_3 = cert44_component_9_41
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_41_3 cert44_layer_9_41_3 23 cert44_layer_9_41_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 9 [])
      LColor.r LColor.p 23 cert44_seen_9_41_4 = cert44_component_9_41
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 9 []) LColor.r LColor.p
    cert44_seen_9_41_4 cert44_layer_9_41_4_eq 23

theorem cert44_step_9_41 :
    closedCollarIndexStepBool word fiber44 9 41 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_9_41)
    (by decide) (by decide)
    (by simpa [cert44_move_9_41] using cert44_component_9_41_eq)
    (by decide) (by decide) (by decide)

def cert44_move_10_4 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_10_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_10_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.b LColor.p cert44_seen_10_4_0 = cert44_layer_10_4_0 := by
  decide

def cert44_seen_10_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_10_4_1 : List ChainEdge :=
  []

theorem cert44_layer_10_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.b LColor.p cert44_seen_10_4_1 = cert44_layer_10_4_1 := by
  decide

theorem cert44_component_10_4_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_10_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_10_22 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_10_22 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_10_22_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_10_22_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_22_0 = cert44_layer_10_22_0 := by
  decide

def cert44_seen_10_22_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_10_22_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_10_22_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_22_1 = cert44_layer_10_22_1 := by
  decide

def cert44_seen_10_22_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_10_22_2 : List ChainEdge :=
  []

theorem cert44_layer_10_22_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.b cert44_seen_10_22_2 = cert44_layer_10_22_2 := by
  decide

theorem cert44_component_10_22_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_10_22 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 27 cert44_seen_10_22_0 = cert44_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_22_0 cert44_layer_10_22_0 26 cert44_layer_10_22_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 26 cert44_seen_10_22_1 = cert44_component_10_22
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_22_1 cert44_layer_10_22_1 25 cert44_layer_10_22_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.b 25 cert44_seen_10_22_2 = cert44_component_10_22
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 10 []) LColor.r LColor.b
    cert44_seen_10_22_2 cert44_layer_10_22_2_eq 25

theorem cert44_step_10_22 :
    closedCollarIndexStepBool word fiber44 10 22 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_10_22)
    (by decide) (by decide)
    (by simpa [cert44_move_10_22] using cert44_component_10_22_eq)
    (by decide) (by decide) (by decide)

def cert44_move_10_36 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_10_36 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_10_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_10_36_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_10_36_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_0 = cert44_layer_10_36_0 := by
  decide

def cert44_seen_10_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_10_36_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_10_36_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_1 = cert44_layer_10_36_1 := by
  decide

def cert44_seen_10_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_10_36_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_10_36_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_2 = cert44_layer_10_36_2 := by
  decide

def cert44_seen_10_36_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_10_36_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_10_36_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_3 = cert44_layer_10_36_3 := by
  decide

def cert44_seen_10_36_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_10_36_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_10_36_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_4 = cert44_layer_10_36_4 := by
  decide

def cert44_seen_10_36_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_10_36_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_10_36_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_5 = cert44_layer_10_36_5 := by
  decide

def cert44_seen_10_36_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_10_36_6 : List ChainEdge :=
  []

theorem cert44_layer_10_36_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 10 [])
      LColor.r LColor.p cert44_seen_10_36_6 = cert44_layer_10_36_6 := by
  decide

theorem cert44_component_10_36_eq :
    closedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_10_36 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 10 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 27 cert44_seen_10_36_0 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_0 cert44_layer_10_36_0 26 cert44_layer_10_36_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 26 cert44_seen_10_36_1 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_1 cert44_layer_10_36_1 25 cert44_layer_10_36_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 25 cert44_seen_10_36_2 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_2 cert44_layer_10_36_2 24 cert44_layer_10_36_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 24 cert44_seen_10_36_3 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_3 cert44_layer_10_36_3 23 cert44_layer_10_36_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 23 cert44_seen_10_36_4 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_4 cert44_layer_10_36_4 22 cert44_layer_10_36_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 22 cert44_seen_10_36_5 = cert44_component_10_36
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_5 cert44_layer_10_36_5 21 cert44_layer_10_36_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 10 [])
      LColor.r LColor.p 21 cert44_seen_10_36_6 = cert44_component_10_36
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 10 []) LColor.r LColor.p
    cert44_seen_10_36_6 cert44_layer_10_36_6_eq 21

theorem cert44_step_10_36 :
    closedCollarIndexStepBool word fiber44 10 36 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_10_36)
    (by decide) (by decide)
    (by simpa [cert44_move_10_36] using cert44_component_10_36_eq)
    (by decide) (by decide) (by decide)

def cert44_move_11_5 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.B6 } }

def cert44_component_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_seen_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }]

def cert44_layer_11_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }]

theorem cert44_layer_11_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.b LColor.p cert44_seen_11_5_0 = cert44_layer_11_5_0 := by
  decide

def cert44_seen_11_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B5 }]

def cert44_layer_11_5_1 : List ChainEdge :=
  []

theorem cert44_layer_11_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.b LColor.p cert44_seen_11_5_1 = cert44_layer_11_5_1 := by
  decide

theorem cert44_component_11_5_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = cert44_component_11_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.B6 } = true := by
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

def cert44_move_11_23 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_11_23 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_11_23_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_11_23_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_23_0 = cert44_layer_11_23_0 := by
  decide

def cert44_seen_11_23_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_11_23_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_11_23_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_23_1 = cert44_layer_11_23_1 := by
  decide

def cert44_seen_11_23_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_11_23_2 : List ChainEdge :=
  []

theorem cert44_layer_11_23_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.b cert44_seen_11_23_2 = cert44_layer_11_23_2 := by
  decide

theorem cert44_component_11_23_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_11_23 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 27 cert44_seen_11_23_0 = cert44_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_23_0 cert44_layer_11_23_0 26 cert44_layer_11_23_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 26 cert44_seen_11_23_1 = cert44_component_11_23
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_23_1 cert44_layer_11_23_1 25 cert44_layer_11_23_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.b 25 cert44_seen_11_23_2 = cert44_component_11_23
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 11 []) LColor.r LColor.b
    cert44_seen_11_23_2 cert44_layer_11_23_2_eq 25

theorem cert44_step_11_23 :
    closedCollarIndexStepBool word fiber44 11 23 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_11_23)
    (by decide) (by decide)
    (by simpa [cert44_move_11_23] using cert44_component_11_23_eq)
    (by decide) (by decide) (by decide)

def cert44_move_11_37 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_11_37 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_11_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_11_37_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_11_37_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_0 = cert44_layer_11_37_0 := by
  decide

def cert44_seen_11_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_11_37_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_11_37_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_1 = cert44_layer_11_37_1 := by
  decide

def cert44_seen_11_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_11_37_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_11_37_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_2 = cert44_layer_11_37_2 := by
  decide

def cert44_seen_11_37_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_11_37_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_11_37_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_3 = cert44_layer_11_37_3 := by
  decide

def cert44_seen_11_37_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_11_37_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_11_37_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_4 = cert44_layer_11_37_4 := by
  decide

def cert44_seen_11_37_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_11_37_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_11_37_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_5 = cert44_layer_11_37_5 := by
  decide

def cert44_seen_11_37_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_11_37_6 : List ChainEdge :=
  []

theorem cert44_layer_11_37_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 11 [])
      LColor.r LColor.p cert44_seen_11_37_6 = cert44_layer_11_37_6 := by
  decide

theorem cert44_component_11_37_eq :
    closedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_11_37 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 11 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 27 cert44_seen_11_37_0 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_0 cert44_layer_11_37_0 26 cert44_layer_11_37_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 26 cert44_seen_11_37_1 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_1 cert44_layer_11_37_1 25 cert44_layer_11_37_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 25 cert44_seen_11_37_2 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_2 cert44_layer_11_37_2 24 cert44_layer_11_37_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 24 cert44_seen_11_37_3 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_3 cert44_layer_11_37_3 23 cert44_layer_11_37_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 23 cert44_seen_11_37_4 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_4 cert44_layer_11_37_4 22 cert44_layer_11_37_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 22 cert44_seen_11_37_5 = cert44_component_11_37
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_5 cert44_layer_11_37_5 21 cert44_layer_11_37_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 11 [])
      LColor.r LColor.p 21 cert44_seen_11_37_6 = cert44_component_11_37
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 11 []) LColor.r LColor.p
    cert44_seen_11_37_6 cert44_layer_11_37_6_eq 21

theorem cert44_step_11_37 :
    closedCollarIndexStepBool word fiber44 11 37 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_11_37)
    (by decide) (by decide)
    (by simpa [cert44_move_11_37] using cert44_component_11_37_eq)
    (by decide) (by decide) (by decide)

def cert44_move_12_0 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_12_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_12_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.b cert44_seen_12_0_0 = cert44_layer_12_0_0 := by
  decide

def cert44_seen_12_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_12_0_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_12_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.b cert44_seen_12_0_1 = cert44_layer_12_0_1 := by
  decide

def cert44_seen_12_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_12_0_2 : List ChainEdge :=
  []

theorem cert44_layer_12_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.b cert44_seen_12_0_2 = cert44_layer_12_0_2 := by
  decide

theorem cert44_component_12_0_eq :
    closedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_12_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 12 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.b 27 cert44_seen_12_0_0 = cert44_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.b
    cert44_seen_12_0_0 cert44_layer_12_0_0 26 cert44_layer_12_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.b 26 cert44_seen_12_0_1 = cert44_component_12_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.b
    cert44_seen_12_0_1 cert44_layer_12_0_1 25 cert44_layer_12_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.b 25 cert44_seen_12_0_2 = cert44_component_12_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 12 []) LColor.r LColor.b
    cert44_seen_12_0_2 cert44_layer_12_0_2_eq 25

theorem cert44_step_12_0 :
    closedCollarIndexStepBool word fiber44 12 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_12_0)
    (by decide) (by decide)
    (by simpa [cert44_move_12_0] using cert44_component_12_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_12_26 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_12_26 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_12_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_12_26_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_12_26_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_26_0 = cert44_layer_12_26_0 := by
  decide

def cert44_seen_12_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_12_26_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_12_26_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_26_1 = cert44_layer_12_26_1 := by
  decide

def cert44_seen_12_26_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_12_26_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_12_26_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_26_2 = cert44_layer_12_26_2 := by
  decide

def cert44_seen_12_26_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_12_26_3 : List ChainEdge :=
  []

theorem cert44_layer_12_26_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 12 [])
      LColor.r LColor.p cert44_seen_12_26_3 = cert44_layer_12_26_3 := by
  decide

theorem cert44_component_12_26_eq :
    closedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_12_26 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 12 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 27 cert44_seen_12_26_0 = cert44_component_12_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_26_0 cert44_layer_12_26_0 26 cert44_layer_12_26_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 26 cert44_seen_12_26_1 = cert44_component_12_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_26_1 cert44_layer_12_26_1 25 cert44_layer_12_26_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 25 cert44_seen_12_26_2 = cert44_component_12_26
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_26_2 cert44_layer_12_26_2 24 cert44_layer_12_26_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 12 [])
      LColor.r LColor.p 24 cert44_seen_12_26_3 = cert44_component_12_26
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 12 []) LColor.r LColor.p
    cert44_seen_12_26_3 cert44_layer_12_26_3_eq 24

theorem cert44_step_12_26 :
    closedCollarIndexStepBool word fiber44 12 26 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_12_26)
    (by decide) (by decide)
    (by simpa [cert44_move_12_26] using cert44_component_12_26_eq)
    (by decide) (by decide) (by decide)

def cert44_move_13_1 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_13_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_13_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.b cert44_seen_13_1_0 = cert44_layer_13_1_0 := by
  decide

def cert44_seen_13_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_13_1_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_13_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.b cert44_seen_13_1_1 = cert44_layer_13_1_1 := by
  decide

def cert44_seen_13_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_13_1_2 : List ChainEdge :=
  []

theorem cert44_layer_13_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.b cert44_seen_13_1_2 = cert44_layer_13_1_2 := by
  decide

theorem cert44_component_13_1_eq :
    closedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_13_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 13 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.b 27 cert44_seen_13_1_0 = cert44_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.b
    cert44_seen_13_1_0 cert44_layer_13_1_0 26 cert44_layer_13_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.b 26 cert44_seen_13_1_1 = cert44_component_13_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.b
    cert44_seen_13_1_1 cert44_layer_13_1_1 25 cert44_layer_13_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.b 25 cert44_seen_13_1_2 = cert44_component_13_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 13 []) LColor.r LColor.b
    cert44_seen_13_1_2 cert44_layer_13_1_2_eq 25

theorem cert44_step_13_1 :
    closedCollarIndexStepBool word fiber44 13 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_13_1)
    (by decide) (by decide)
    (by simpa [cert44_move_13_1] using cert44_component_13_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_13_27 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_13_27 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_13_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_13_27_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_13_27_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_27_0 = cert44_layer_13_27_0 := by
  decide

def cert44_seen_13_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_13_27_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_13_27_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_27_1 = cert44_layer_13_27_1 := by
  decide

def cert44_seen_13_27_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_13_27_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_13_27_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_27_2 = cert44_layer_13_27_2 := by
  decide

def cert44_seen_13_27_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_13_27_3 : List ChainEdge :=
  []

theorem cert44_layer_13_27_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 13 [])
      LColor.r LColor.p cert44_seen_13_27_3 = cert44_layer_13_27_3 := by
  decide

theorem cert44_component_13_27_eq :
    closedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_13_27 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 13 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 27 cert44_seen_13_27_0 = cert44_component_13_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_27_0 cert44_layer_13_27_0 26 cert44_layer_13_27_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 26 cert44_seen_13_27_1 = cert44_component_13_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_27_1 cert44_layer_13_27_1 25 cert44_layer_13_27_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 25 cert44_seen_13_27_2 = cert44_component_13_27
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_27_2 cert44_layer_13_27_2 24 cert44_layer_13_27_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 13 [])
      LColor.r LColor.p 24 cert44_seen_13_27_3 = cert44_component_13_27
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 13 []) LColor.r LColor.p
    cert44_seen_13_27_3 cert44_layer_13_27_3_eq 24

theorem cert44_step_13_27 :
    closedCollarIndexStepBool word fiber44 13 27 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_13_27)
    (by decide) (by decide)
    (by simpa [cert44_move_13_27] using cert44_component_13_27_eq)
    (by decide) (by decide) (by decide)

def cert44_move_14_2 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_14_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_14_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.b cert44_seen_14_2_0 = cert44_layer_14_2_0 := by
  decide

def cert44_seen_14_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_14_2_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_14_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.b cert44_seen_14_2_1 = cert44_layer_14_2_1 := by
  decide

def cert44_seen_14_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_14_2_2 : List ChainEdge :=
  []

theorem cert44_layer_14_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.b cert44_seen_14_2_2 = cert44_layer_14_2_2 := by
  decide

theorem cert44_component_14_2_eq :
    closedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_14_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 14 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.b 27 cert44_seen_14_2_0 = cert44_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.b
    cert44_seen_14_2_0 cert44_layer_14_2_0 26 cert44_layer_14_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.b 26 cert44_seen_14_2_1 = cert44_component_14_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.b
    cert44_seen_14_2_1 cert44_layer_14_2_1 25 cert44_layer_14_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.b 25 cert44_seen_14_2_2 = cert44_component_14_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 14 []) LColor.r LColor.b
    cert44_seen_14_2_2 cert44_layer_14_2_2_eq 25

theorem cert44_step_14_2 :
    closedCollarIndexStepBool word fiber44 14 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_14_2)
    (by decide) (by decide)
    (by simpa [cert44_move_14_2] using cert44_component_14_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_14_28 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_14_28 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_14_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_14_28_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_14_28_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_28_0 = cert44_layer_14_28_0 := by
  decide

def cert44_seen_14_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_14_28_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_14_28_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_28_1 = cert44_layer_14_28_1 := by
  decide

def cert44_seen_14_28_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_14_28_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_14_28_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_28_2 = cert44_layer_14_28_2 := by
  decide

def cert44_seen_14_28_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_14_28_3 : List ChainEdge :=
  []

theorem cert44_layer_14_28_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 14 [])
      LColor.r LColor.p cert44_seen_14_28_3 = cert44_layer_14_28_3 := by
  decide

theorem cert44_component_14_28_eq :
    closedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_14_28 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 14 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 27 cert44_seen_14_28_0 = cert44_component_14_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_28_0 cert44_layer_14_28_0 26 cert44_layer_14_28_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 26 cert44_seen_14_28_1 = cert44_component_14_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_28_1 cert44_layer_14_28_1 25 cert44_layer_14_28_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 25 cert44_seen_14_28_2 = cert44_component_14_28
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_28_2 cert44_layer_14_28_2 24 cert44_layer_14_28_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 14 [])
      LColor.r LColor.p 24 cert44_seen_14_28_3 = cert44_component_14_28
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 14 []) LColor.r LColor.p
    cert44_seen_14_28_3 cert44_layer_14_28_3_eq 24

theorem cert44_step_14_28 :
    closedCollarIndexStepBool word fiber44 14 28 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_14_28)
    (by decide) (by decide)
    (by simpa [cert44_move_14_28] using cert44_component_14_28_eq)
    (by decide) (by decide) (by decide)

def cert44_move_15_3 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_15_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_15_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.b cert44_seen_15_3_0 = cert44_layer_15_3_0 := by
  decide

def cert44_seen_15_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_15_3_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_15_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.b cert44_seen_15_3_1 = cert44_layer_15_3_1 := by
  decide

def cert44_seen_15_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_15_3_2 : List ChainEdge :=
  []

theorem cert44_layer_15_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.b cert44_seen_15_3_2 = cert44_layer_15_3_2 := by
  decide

theorem cert44_component_15_3_eq :
    closedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_15_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 15 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.b 27 cert44_seen_15_3_0 = cert44_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.b
    cert44_seen_15_3_0 cert44_layer_15_3_0 26 cert44_layer_15_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.b 26 cert44_seen_15_3_1 = cert44_component_15_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.b
    cert44_seen_15_3_1 cert44_layer_15_3_1 25 cert44_layer_15_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.b 25 cert44_seen_15_3_2 = cert44_component_15_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 15 []) LColor.r LColor.b
    cert44_seen_15_3_2 cert44_layer_15_3_2_eq 25

theorem cert44_step_15_3 :
    closedCollarIndexStepBool word fiber44 15 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_15_3)
    (by decide) (by decide)
    (by simpa [cert44_move_15_3] using cert44_component_15_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_15_29 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_15_29 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_15_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_15_29_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_15_29_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_29_0 = cert44_layer_15_29_0 := by
  decide

def cert44_seen_15_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_15_29_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_15_29_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_29_1 = cert44_layer_15_29_1 := by
  decide

def cert44_seen_15_29_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_15_29_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_15_29_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_29_2 = cert44_layer_15_29_2 := by
  decide

def cert44_seen_15_29_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_15_29_3 : List ChainEdge :=
  []

theorem cert44_layer_15_29_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 15 [])
      LColor.r LColor.p cert44_seen_15_29_3 = cert44_layer_15_29_3 := by
  decide

theorem cert44_component_15_29_eq :
    closedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_15_29 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 15 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 27 cert44_seen_15_29_0 = cert44_component_15_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_29_0 cert44_layer_15_29_0 26 cert44_layer_15_29_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 26 cert44_seen_15_29_1 = cert44_component_15_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_29_1 cert44_layer_15_29_1 25 cert44_layer_15_29_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 25 cert44_seen_15_29_2 = cert44_component_15_29
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_29_2 cert44_layer_15_29_2 24 cert44_layer_15_29_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 15 [])
      LColor.r LColor.p 24 cert44_seen_15_29_3 = cert44_component_15_29
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 15 []) LColor.r LColor.p
    cert44_seen_15_29_3 cert44_layer_15_29_3_eq 24

theorem cert44_step_15_29 :
    closedCollarIndexStepBool word fiber44 15 29 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_15_29)
    (by decide) (by decide)
    (by simpa [cert44_move_15_29] using cert44_component_15_29_eq)
    (by decide) (by decide) (by decide)

def cert44_move_16_4 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_16_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_16_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.b cert44_seen_16_4_0 = cert44_layer_16_4_0 := by
  decide

def cert44_seen_16_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_16_4_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_16_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.b cert44_seen_16_4_1 = cert44_layer_16_4_1 := by
  decide

def cert44_seen_16_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_16_4_2 : List ChainEdge :=
  []

theorem cert44_layer_16_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.b cert44_seen_16_4_2 = cert44_layer_16_4_2 := by
  decide

theorem cert44_component_16_4_eq :
    closedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_16_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 16 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.b 27 cert44_seen_16_4_0 = cert44_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.b
    cert44_seen_16_4_0 cert44_layer_16_4_0 26 cert44_layer_16_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.b 26 cert44_seen_16_4_1 = cert44_component_16_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.b
    cert44_seen_16_4_1 cert44_layer_16_4_1 25 cert44_layer_16_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.b 25 cert44_seen_16_4_2 = cert44_component_16_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 16 []) LColor.r LColor.b
    cert44_seen_16_4_2 cert44_layer_16_4_2_eq 25

theorem cert44_step_16_4 :
    closedCollarIndexStepBool word fiber44 16 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_16_4)
    (by decide) (by decide)
    (by simpa [cert44_move_16_4] using cert44_component_16_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_16_24 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_16_24 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_16_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_16_24_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_16_24_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_0 = cert44_layer_16_24_0 := by
  decide

def cert44_seen_16_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_16_24_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_16_24_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_1 = cert44_layer_16_24_1 := by
  decide

def cert44_seen_16_24_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_16_24_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_16_24_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_2 = cert44_layer_16_24_2 := by
  decide

def cert44_seen_16_24_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_16_24_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_16_24_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_3 = cert44_layer_16_24_3 := by
  decide

def cert44_seen_16_24_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_16_24_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_16_24_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_4 = cert44_layer_16_24_4 := by
  decide

def cert44_seen_16_24_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_16_24_5 : List ChainEdge :=
  []

theorem cert44_layer_16_24_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 16 [])
      LColor.r LColor.p cert44_seen_16_24_5 = cert44_layer_16_24_5 := by
  decide

theorem cert44_component_16_24_eq :
    closedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_16_24 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 16 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 27 cert44_seen_16_24_0 = cert44_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_0 cert44_layer_16_24_0 26 cert44_layer_16_24_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 26 cert44_seen_16_24_1 = cert44_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_1 cert44_layer_16_24_1 25 cert44_layer_16_24_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 25 cert44_seen_16_24_2 = cert44_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_2 cert44_layer_16_24_2 24 cert44_layer_16_24_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 24 cert44_seen_16_24_3 = cert44_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_3 cert44_layer_16_24_3 23 cert44_layer_16_24_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 23 cert44_seen_16_24_4 = cert44_component_16_24
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_4 cert44_layer_16_24_4 22 cert44_layer_16_24_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 16 [])
      LColor.r LColor.p 22 cert44_seen_16_24_5 = cert44_component_16_24
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 16 []) LColor.r LColor.p
    cert44_seen_16_24_5 cert44_layer_16_24_5_eq 22

theorem cert44_step_16_24 :
    closedCollarIndexStepBool word fiber44 16 24 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_16_24)
    (by decide) (by decide)
    (by simpa [cert44_move_16_24] using cert44_component_16_24_eq)
    (by decide) (by decide) (by decide)

def cert44_move_17_5 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_17_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_17_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.b cert44_seen_17_5_0 = cert44_layer_17_5_0 := by
  decide

def cert44_seen_17_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_17_5_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_17_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.b cert44_seen_17_5_1 = cert44_layer_17_5_1 := by
  decide

def cert44_seen_17_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_17_5_2 : List ChainEdge :=
  []

theorem cert44_layer_17_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.b cert44_seen_17_5_2 = cert44_layer_17_5_2 := by
  decide

theorem cert44_component_17_5_eq :
    closedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_17_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 17 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.b 27 cert44_seen_17_5_0 = cert44_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.b
    cert44_seen_17_5_0 cert44_layer_17_5_0 26 cert44_layer_17_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.b 26 cert44_seen_17_5_1 = cert44_component_17_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.b
    cert44_seen_17_5_1 cert44_layer_17_5_1 25 cert44_layer_17_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.b 25 cert44_seen_17_5_2 = cert44_component_17_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 17 []) LColor.r LColor.b
    cert44_seen_17_5_2 cert44_layer_17_5_2_eq 25

theorem cert44_step_17_5 :
    closedCollarIndexStepBool word fiber44 17 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_17_5)
    (by decide) (by decide)
    (by simpa [cert44_move_17_5] using cert44_component_17_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_17_25 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_17_25 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_17_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_17_25_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_17_25_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_0 = cert44_layer_17_25_0 := by
  decide

def cert44_seen_17_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_17_25_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_17_25_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_1 = cert44_layer_17_25_1 := by
  decide

def cert44_seen_17_25_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_17_25_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_17_25_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_2 = cert44_layer_17_25_2 := by
  decide

def cert44_seen_17_25_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_17_25_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_17_25_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_3 = cert44_layer_17_25_3 := by
  decide

def cert44_seen_17_25_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_17_25_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_17_25_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_4 = cert44_layer_17_25_4 := by
  decide

def cert44_seen_17_25_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_17_25_5 : List ChainEdge :=
  []

theorem cert44_layer_17_25_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 17 [])
      LColor.r LColor.p cert44_seen_17_25_5 = cert44_layer_17_25_5 := by
  decide

theorem cert44_component_17_25_eq :
    closedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_17_25 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 17 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 27 cert44_seen_17_25_0 = cert44_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_0 cert44_layer_17_25_0 26 cert44_layer_17_25_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 26 cert44_seen_17_25_1 = cert44_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_1 cert44_layer_17_25_1 25 cert44_layer_17_25_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 25 cert44_seen_17_25_2 = cert44_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_2 cert44_layer_17_25_2 24 cert44_layer_17_25_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 24 cert44_seen_17_25_3 = cert44_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_3 cert44_layer_17_25_3 23 cert44_layer_17_25_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 23 cert44_seen_17_25_4 = cert44_component_17_25
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_4 cert44_layer_17_25_4 22 cert44_layer_17_25_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 17 [])
      LColor.r LColor.p 22 cert44_seen_17_25_5 = cert44_component_17_25
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 17 []) LColor.r LColor.p
    cert44_seen_17_25_5 cert44_layer_17_25_5_eq 22

theorem cert44_step_17_25 :
    closedCollarIndexStepBool word fiber44 17 25 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_17_25)
    (by decide) (by decide)
    (by simpa [cert44_move_17_25] using cert44_component_17_25_eq)
    (by decide) (by decide) (by decide)

def cert44_move_18_6 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_18_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_18_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_18_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_6_0 = cert44_layer_18_6_0 := by
  decide

def cert44_seen_18_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_18_6_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_18_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_6_1 = cert44_layer_18_6_1 := by
  decide

def cert44_seen_18_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_18_6_2 : List ChainEdge :=
  []

theorem cert44_layer_18_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 18 [])
      LColor.r LColor.b cert44_seen_18_6_2 = cert44_layer_18_6_2 := by
  decide

theorem cert44_component_18_6_eq :
    closedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_18_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 18 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 27 cert44_seen_18_6_0 = cert44_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_6_0 cert44_layer_18_6_0 26 cert44_layer_18_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 26 cert44_seen_18_6_1 = cert44_component_18_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_6_1 cert44_layer_18_6_1 25 cert44_layer_18_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 18 [])
      LColor.r LColor.b 25 cert44_seen_18_6_2 = cert44_component_18_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 18 []) LColor.r LColor.b
    cert44_seen_18_6_2 cert44_layer_18_6_2_eq 25

theorem cert44_step_18_6 :
    closedCollarIndexStepBool word fiber44 18 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_18_6)
    (by decide) (by decide)
    (by simpa [cert44_move_18_6] using cert44_component_18_6_eq)
    (by decide) (by decide) (by decide)

def cert44_move_19_7 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_19_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_19_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_19_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_7_0 = cert44_layer_19_7_0 := by
  decide

def cert44_seen_19_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_19_7_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_19_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_7_1 = cert44_layer_19_7_1 := by
  decide

def cert44_seen_19_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_19_7_2 : List ChainEdge :=
  []

theorem cert44_layer_19_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 19 [])
      LColor.r LColor.b cert44_seen_19_7_2 = cert44_layer_19_7_2 := by
  decide

theorem cert44_component_19_7_eq :
    closedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_19_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 19 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 27 cert44_seen_19_7_0 = cert44_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_7_0 cert44_layer_19_7_0 26 cert44_layer_19_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 26 cert44_seen_19_7_1 = cert44_component_19_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_7_1 cert44_layer_19_7_1 25 cert44_layer_19_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 19 [])
      LColor.r LColor.b 25 cert44_seen_19_7_2 = cert44_component_19_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 19 []) LColor.r LColor.b
    cert44_seen_19_7_2 cert44_layer_19_7_2_eq 25

theorem cert44_step_19_7 :
    closedCollarIndexStepBool word fiber44 19 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_19_7)
    (by decide) (by decide)
    (by simpa [cert44_move_19_7] using cert44_component_19_7_eq)
    (by decide) (by decide) (by decide)

def cert44_move_20_8 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_20_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_20_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_20_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_8_0 = cert44_layer_20_8_0 := by
  decide

def cert44_seen_20_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_20_8_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_20_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_8_1 = cert44_layer_20_8_1 := by
  decide

def cert44_seen_20_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_20_8_2 : List ChainEdge :=
  []

theorem cert44_layer_20_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 20 [])
      LColor.r LColor.b cert44_seen_20_8_2 = cert44_layer_20_8_2 := by
  decide

theorem cert44_component_20_8_eq :
    closedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_20_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 20 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 27 cert44_seen_20_8_0 = cert44_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_8_0 cert44_layer_20_8_0 26 cert44_layer_20_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 26 cert44_seen_20_8_1 = cert44_component_20_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_8_1 cert44_layer_20_8_1 25 cert44_layer_20_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 20 [])
      LColor.r LColor.b 25 cert44_seen_20_8_2 = cert44_component_20_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 20 []) LColor.r LColor.b
    cert44_seen_20_8_2 cert44_layer_20_8_2_eq 25

theorem cert44_step_20_8 :
    closedCollarIndexStepBool word fiber44 20 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_20_8)
    (by decide) (by decide)
    (by simpa [cert44_move_20_8] using cert44_component_20_8_eq)
    (by decide) (by decide) (by decide)

def cert44_move_21_9 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_21_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_21_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_21_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_9_0 = cert44_layer_21_9_0 := by
  decide

def cert44_seen_21_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_21_9_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_21_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_9_1 = cert44_layer_21_9_1 := by
  decide

def cert44_seen_21_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_21_9_2 : List ChainEdge :=
  []

theorem cert44_layer_21_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 21 [])
      LColor.r LColor.b cert44_seen_21_9_2 = cert44_layer_21_9_2 := by
  decide

theorem cert44_component_21_9_eq :
    closedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_21_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 21 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 27 cert44_seen_21_9_0 = cert44_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_9_0 cert44_layer_21_9_0 26 cert44_layer_21_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 26 cert44_seen_21_9_1 = cert44_component_21_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_9_1 cert44_layer_21_9_1 25 cert44_layer_21_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 21 [])
      LColor.r LColor.b 25 cert44_seen_21_9_2 = cert44_component_21_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 21 []) LColor.r LColor.b
    cert44_seen_21_9_2 cert44_layer_21_9_2_eq 25

theorem cert44_step_21_9 :
    closedCollarIndexStepBool word fiber44 21 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_21_9)
    (by decide) (by decide)
    (by simpa [cert44_move_21_9] using cert44_component_21_9_eq)
    (by decide) (by decide) (by decide)

def cert44_move_22_10 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_22_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_22_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_22_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.b cert44_seen_22_10_0 = cert44_layer_22_10_0 := by
  decide

def cert44_seen_22_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_22_10_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_22_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.b cert44_seen_22_10_1 = cert44_layer_22_10_1 := by
  decide

def cert44_seen_22_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_22_10_2 : List ChainEdge :=
  []

theorem cert44_layer_22_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 22 [])
      LColor.r LColor.b cert44_seen_22_10_2 = cert44_layer_22_10_2 := by
  decide

theorem cert44_component_22_10_eq :
    closedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_22_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 22 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.b 27 cert44_seen_22_10_0 = cert44_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 22 []) LColor.r LColor.b
    cert44_seen_22_10_0 cert44_layer_22_10_0 26 cert44_layer_22_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.b 26 cert44_seen_22_10_1 = cert44_component_22_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 22 []) LColor.r LColor.b
    cert44_seen_22_10_1 cert44_layer_22_10_1 25 cert44_layer_22_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 22 [])
      LColor.r LColor.b 25 cert44_seen_22_10_2 = cert44_component_22_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 22 []) LColor.r LColor.b
    cert44_seen_22_10_2 cert44_layer_22_10_2_eq 25

theorem cert44_step_22_10 :
    closedCollarIndexStepBool word fiber44 22 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_22_10)
    (by decide) (by decide)
    (by simpa [cert44_move_22_10] using cert44_component_22_10_eq)
    (by decide) (by decide) (by decide)

def cert44_move_23_11 : ChainMove :=
  { a := LColor.r, c := LColor.b, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_23_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_23_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_23_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.b cert44_seen_23_11_0 = cert44_layer_23_11_0 := by
  decide

def cert44_seen_23_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_23_11_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_23_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.b cert44_seen_23_11_1 = cert44_layer_23_11_1 := by
  decide

def cert44_seen_23_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B6 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_23_11_2 : List ChainEdge :=
  []

theorem cert44_layer_23_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 23 [])
      LColor.r LColor.b cert44_seen_23_11_2 = cert44_layer_23_11_2 := by
  decide

theorem cert44_component_23_11_eq :
    closedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = cert44_component_23_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 23 [])
      LColor.r LColor.b { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.b 27 cert44_seen_23_11_0 = cert44_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 23 []) LColor.r LColor.b
    cert44_seen_23_11_0 cert44_layer_23_11_0 26 cert44_layer_23_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.b 26 cert44_seen_23_11_1 = cert44_component_23_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 23 []) LColor.r LColor.b
    cert44_seen_23_11_1 cert44_layer_23_11_1 25 cert44_layer_23_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 23 [])
      LColor.r LColor.b 25 cert44_seen_23_11_2 = cert44_component_23_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 23 []) LColor.r LColor.b
    cert44_seen_23_11_2 cert44_layer_23_11_2_eq 25

theorem cert44_step_23_11 :
    closedCollarIndexStepBool word fiber44 23 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_23_11)
    (by decide) (by decide)
    (by simpa [cert44_move_23_11] using cert44_component_23_11_eq)
    (by decide) (by decide) (by decide)

def cert44_move_24_16 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_24_16 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_24_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_24_16_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_24_16_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_0 = cert44_layer_24_16_0 := by
  decide

def cert44_seen_24_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_24_16_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_24_16_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_1 = cert44_layer_24_16_1 := by
  decide

def cert44_seen_24_16_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_24_16_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_24_16_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_2 = cert44_layer_24_16_2 := by
  decide

def cert44_seen_24_16_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_24_16_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_24_16_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_3 = cert44_layer_24_16_3 := by
  decide

def cert44_seen_24_16_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_24_16_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_24_16_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_4 = cert44_layer_24_16_4 := by
  decide

def cert44_seen_24_16_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_24_16_5 : List ChainEdge :=
  []

theorem cert44_layer_24_16_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 24 [])
      LColor.r LColor.p cert44_seen_24_16_5 = cert44_layer_24_16_5 := by
  decide

theorem cert44_component_24_16_eq :
    closedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_24_16 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 24 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 27 cert44_seen_24_16_0 = cert44_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_0 cert44_layer_24_16_0 26 cert44_layer_24_16_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 26 cert44_seen_24_16_1 = cert44_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_1 cert44_layer_24_16_1 25 cert44_layer_24_16_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 25 cert44_seen_24_16_2 = cert44_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_2 cert44_layer_24_16_2 24 cert44_layer_24_16_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 24 cert44_seen_24_16_3 = cert44_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_3 cert44_layer_24_16_3 23 cert44_layer_24_16_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 23 cert44_seen_24_16_4 = cert44_component_24_16
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_4 cert44_layer_24_16_4 22 cert44_layer_24_16_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 24 [])
      LColor.r LColor.p 22 cert44_seen_24_16_5 = cert44_component_24_16
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 24 []) LColor.r LColor.p
    cert44_seen_24_16_5 cert44_layer_24_16_5_eq 22

theorem cert44_step_24_16 :
    closedCollarIndexStepBool word fiber44 24 16 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_24_16)
    (by decide) (by decide)
    (by simpa [cert44_move_24_16] using cert44_component_24_16_eq)
    (by decide) (by decide) (by decide)

def cert44_move_25_17 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_25_17 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_seen_25_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_25_17_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_25_17_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_0 = cert44_layer_25_17_0 := by
  decide

def cert44_seen_25_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_25_17_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_25_17_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_1 = cert44_layer_25_17_1 := by
  decide

def cert44_seen_25_17_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_25_17_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_25_17_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_2 = cert44_layer_25_17_2 := by
  decide

def cert44_seen_25_17_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_25_17_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_25_17_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_3 = cert44_layer_25_17_3 := by
  decide

def cert44_seen_25_17_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_25_17_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_25_17_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_4 = cert44_layer_25_17_4 := by
  decide

def cert44_seen_25_17_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.B4 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F2F4 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_25_17_5 : List ChainEdge :=
  []

theorem cert44_layer_25_17_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 25 [])
      LColor.r LColor.p cert44_seen_25_17_5 = cert44_layer_25_17_5 := by
  decide

theorem cert44_component_25_17_eq :
    closedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_25_17 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 25 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 27 cert44_seen_25_17_0 = cert44_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_0 cert44_layer_25_17_0 26 cert44_layer_25_17_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 26 cert44_seen_25_17_1 = cert44_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_1 cert44_layer_25_17_1 25 cert44_layer_25_17_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 25 cert44_seen_25_17_2 = cert44_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_2 cert44_layer_25_17_2 24 cert44_layer_25_17_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 24 cert44_seen_25_17_3 = cert44_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_3 cert44_layer_25_17_3 23 cert44_layer_25_17_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 23 cert44_seen_25_17_4 = cert44_component_25_17
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_4 cert44_layer_25_17_4 22 cert44_layer_25_17_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 25 [])
      LColor.r LColor.p 22 cert44_seen_25_17_5 = cert44_component_25_17
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 25 []) LColor.r LColor.p
    cert44_seen_25_17_5 cert44_layer_25_17_5_eq 22

theorem cert44_step_25_17 :
    closedCollarIndexStepBool word fiber44 25 17 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_25_17)
    (by decide) (by decide)
    (by simpa [cert44_move_25_17] using cert44_component_25_17_eq)
    (by decide) (by decide) (by decide)

def cert44_move_26_12 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_26_12 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_26_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_26_12_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_26_12_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.p cert44_seen_26_12_0 = cert44_layer_26_12_0 := by
  decide

def cert44_seen_26_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_26_12_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_26_12_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.p cert44_seen_26_12_1 = cert44_layer_26_12_1 := by
  decide

def cert44_seen_26_12_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_26_12_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_26_12_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.p cert44_seen_26_12_2 = cert44_layer_26_12_2 := by
  decide

def cert44_seen_26_12_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_26_12_3 : List ChainEdge :=
  []

theorem cert44_layer_26_12_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 26 [])
      LColor.r LColor.p cert44_seen_26_12_3 = cert44_layer_26_12_3 := by
  decide

theorem cert44_component_26_12_eq :
    closedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_26_12 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 26 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.p 27 cert44_seen_26_12_0 = cert44_component_26_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.p
    cert44_seen_26_12_0 cert44_layer_26_12_0 26 cert44_layer_26_12_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.p 26 cert44_seen_26_12_1 = cert44_component_26_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.p
    cert44_seen_26_12_1 cert44_layer_26_12_1 25 cert44_layer_26_12_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.p 25 cert44_seen_26_12_2 = cert44_component_26_12
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 26 []) LColor.r LColor.p
    cert44_seen_26_12_2 cert44_layer_26_12_2 24 cert44_layer_26_12_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 26 [])
      LColor.r LColor.p 24 cert44_seen_26_12_3 = cert44_component_26_12
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 26 []) LColor.r LColor.p
    cert44_seen_26_12_3 cert44_layer_26_12_3_eq 24

theorem cert44_step_26_12 :
    closedCollarIndexStepBool word fiber44 26 12 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_26_12)
    (by decide) (by decide)
    (by simpa [cert44_move_26_12] using cert44_component_26_12_eq)
    (by decide) (by decide) (by decide)

def cert44_move_27_13 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_27_13 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_27_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_27_13_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_27_13_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.p cert44_seen_27_13_0 = cert44_layer_27_13_0 := by
  decide

def cert44_seen_27_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_27_13_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_27_13_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.p cert44_seen_27_13_1 = cert44_layer_27_13_1 := by
  decide

def cert44_seen_27_13_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_27_13_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_27_13_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.p cert44_seen_27_13_2 = cert44_layer_27_13_2 := by
  decide

def cert44_seen_27_13_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_27_13_3 : List ChainEdge :=
  []

theorem cert44_layer_27_13_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 27 [])
      LColor.r LColor.p cert44_seen_27_13_3 = cert44_layer_27_13_3 := by
  decide

theorem cert44_component_27_13_eq :
    closedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_27_13 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 27 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.p 27 cert44_seen_27_13_0 = cert44_component_27_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.p
    cert44_seen_27_13_0 cert44_layer_27_13_0 26 cert44_layer_27_13_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.p 26 cert44_seen_27_13_1 = cert44_component_27_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.p
    cert44_seen_27_13_1 cert44_layer_27_13_1 25 cert44_layer_27_13_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.p 25 cert44_seen_27_13_2 = cert44_component_27_13
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 27 []) LColor.r LColor.p
    cert44_seen_27_13_2 cert44_layer_27_13_2 24 cert44_layer_27_13_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 27 [])
      LColor.r LColor.p 24 cert44_seen_27_13_3 = cert44_component_27_13
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 27 []) LColor.r LColor.p
    cert44_seen_27_13_3 cert44_layer_27_13_3_eq 24

theorem cert44_step_27_13 :
    closedCollarIndexStepBool word fiber44 27 13 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_27_13)
    (by decide) (by decide)
    (by simpa [cert44_move_27_13] using cert44_component_27_13_eq)
    (by decide) (by decide) (by decide)

def cert44_move_28_14 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_28_14 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_28_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_28_14_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_28_14_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.p cert44_seen_28_14_0 = cert44_layer_28_14_0 := by
  decide

def cert44_seen_28_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_28_14_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_28_14_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.p cert44_seen_28_14_1 = cert44_layer_28_14_1 := by
  decide

def cert44_seen_28_14_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_28_14_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_28_14_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.p cert44_seen_28_14_2 = cert44_layer_28_14_2 := by
  decide

def cert44_seen_28_14_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_28_14_3 : List ChainEdge :=
  []

theorem cert44_layer_28_14_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 28 [])
      LColor.r LColor.p cert44_seen_28_14_3 = cert44_layer_28_14_3 := by
  decide

theorem cert44_component_28_14_eq :
    closedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_28_14 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 28 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.p 27 cert44_seen_28_14_0 = cert44_component_28_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.p
    cert44_seen_28_14_0 cert44_layer_28_14_0 26 cert44_layer_28_14_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.p 26 cert44_seen_28_14_1 = cert44_component_28_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.p
    cert44_seen_28_14_1 cert44_layer_28_14_1 25 cert44_layer_28_14_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.p 25 cert44_seen_28_14_2 = cert44_component_28_14
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 28 []) LColor.r LColor.p
    cert44_seen_28_14_2 cert44_layer_28_14_2 24 cert44_layer_28_14_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 28 [])
      LColor.r LColor.p 24 cert44_seen_28_14_3 = cert44_component_28_14
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 28 []) LColor.r LColor.p
    cert44_seen_28_14_3 cert44_layer_28_14_3_eq 24

theorem cert44_step_28_14 :
    closedCollarIndexStepBool word fiber44 28 14 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_28_14)
    (by decide) (by decide)
    (by simpa [cert44_move_28_14] using cert44_component_28_14_eq)
    (by decide) (by decide) (by decide)

def cert44_move_29_15 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_29_15 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_seen_29_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_29_15_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_29_15_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.p cert44_seen_29_15_0 = cert44_layer_29_15_0 := by
  decide

def cert44_seen_29_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_29_15_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_29_15_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.p cert44_seen_29_15_1 = cert44_layer_29_15_1 := by
  decide

def cert44_seen_29_15_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_29_15_2 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_29_15_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.p cert44_seen_29_15_2 = cert44_layer_29_15_2 := by
  decide

def cert44_seen_29_15_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_29_15_3 : List ChainEdge :=
  []

theorem cert44_layer_29_15_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 29 [])
      LColor.r LColor.p cert44_seen_29_15_3 = cert44_layer_29_15_3 := by
  decide

theorem cert44_component_29_15_eq :
    closedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_29_15 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 29 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.p 27 cert44_seen_29_15_0 = cert44_component_29_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.p
    cert44_seen_29_15_0 cert44_layer_29_15_0 26 cert44_layer_29_15_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.p 26 cert44_seen_29_15_1 = cert44_component_29_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.p
    cert44_seen_29_15_1 cert44_layer_29_15_1 25 cert44_layer_29_15_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.p 25 cert44_seen_29_15_2 = cert44_component_29_15
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 29 []) LColor.r LColor.p
    cert44_seen_29_15_2 cert44_layer_29_15_2 24 cert44_layer_29_15_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 29 [])
      LColor.r LColor.p 24 cert44_seen_29_15_3 = cert44_component_29_15
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 29 []) LColor.r LColor.p
    cert44_seen_29_15_3 cert44_layer_29_15_3_eq 24

theorem cert44_step_29_15 :
    closedCollarIndexStepBool word fiber44 29 15 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_29_15)
    (by decide) (by decide)
    (by simpa [cert44_move_29_15] using cert44_component_29_15_eq)
    (by decide) (by decide) (by decide)

def cert44_move_30_42 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_30_42 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_30_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_30_42_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_30_42_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.b LColor.p cert44_seen_30_42_0 = cert44_layer_30_42_0 := by
  decide

def cert44_seen_30_42_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_30_42_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_30_42_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.b LColor.p cert44_seen_30_42_1 = cert44_layer_30_42_1 := by
  decide

def cert44_seen_30_42_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_30_42_2 : List ChainEdge :=
  []

theorem cert44_layer_30_42_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 30 [])
      LColor.b LColor.p cert44_seen_30_42_2 = cert44_layer_30_42_2 := by
  decide

theorem cert44_component_30_42_eq :
    closedCollarComponent word (listGetD fiber44 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_30_42 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 30 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.b LColor.p 27 cert44_seen_30_42_0 = cert44_component_30_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 30 []) LColor.b LColor.p
    cert44_seen_30_42_0 cert44_layer_30_42_0 26 cert44_layer_30_42_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.b LColor.p 26 cert44_seen_30_42_1 = cert44_component_30_42
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 30 []) LColor.b LColor.p
    cert44_seen_30_42_1 cert44_layer_30_42_1 25 cert44_layer_30_42_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 30 [])
      LColor.b LColor.p 25 cert44_seen_30_42_2 = cert44_component_30_42
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 30 []) LColor.b LColor.p
    cert44_seen_30_42_2 cert44_layer_30_42_2_eq 25

theorem cert44_step_30_42 :
    closedCollarIndexStepBool word fiber44 30 42 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_30_42)
    (by decide) (by decide)
    (by simpa [cert44_move_30_42] using cert44_component_30_42_eq)
    (by decide) (by decide) (by decide)

def cert44_move_31_43 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_31_43 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_31_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_31_43_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_31_43_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.b LColor.p cert44_seen_31_43_0 = cert44_layer_31_43_0 := by
  decide

def cert44_seen_31_43_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_31_43_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_31_43_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.b LColor.p cert44_seen_31_43_1 = cert44_layer_31_43_1 := by
  decide

def cert44_seen_31_43_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_31_43_2 : List ChainEdge :=
  []

theorem cert44_layer_31_43_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 31 [])
      LColor.b LColor.p cert44_seen_31_43_2 = cert44_layer_31_43_2 := by
  decide

theorem cert44_component_31_43_eq :
    closedCollarComponent word (listGetD fiber44 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_31_43 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 31 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.b LColor.p 27 cert44_seen_31_43_0 = cert44_component_31_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 31 []) LColor.b LColor.p
    cert44_seen_31_43_0 cert44_layer_31_43_0 26 cert44_layer_31_43_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.b LColor.p 26 cert44_seen_31_43_1 = cert44_component_31_43
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 31 []) LColor.b LColor.p
    cert44_seen_31_43_1 cert44_layer_31_43_1 25 cert44_layer_31_43_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 31 [])
      LColor.b LColor.p 25 cert44_seen_31_43_2 = cert44_component_31_43
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 31 []) LColor.b LColor.p
    cert44_seen_31_43_2 cert44_layer_31_43_2_eq 25

theorem cert44_step_31_43 :
    closedCollarIndexStepBool word fiber44 31 43 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_31_43)
    (by decide) (by decide)
    (by simpa [cert44_move_31_43] using cert44_component_31_43_eq)
    (by decide) (by decide) (by decide)

def cert44_move_32_44 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_32_44 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_32_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_32_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_32_44_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.b LColor.p cert44_seen_32_44_0 = cert44_layer_32_44_0 := by
  decide

def cert44_seen_32_44_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_32_44_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_32_44_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.b LColor.p cert44_seen_32_44_1 = cert44_layer_32_44_1 := by
  decide

def cert44_seen_32_44_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_32_44_2 : List ChainEdge :=
  []

theorem cert44_layer_32_44_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 32 [])
      LColor.b LColor.p cert44_seen_32_44_2 = cert44_layer_32_44_2 := by
  decide

theorem cert44_component_32_44_eq :
    closedCollarComponent word (listGetD fiber44 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_32_44 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 32 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.b LColor.p 27 cert44_seen_32_44_0 = cert44_component_32_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 32 []) LColor.b LColor.p
    cert44_seen_32_44_0 cert44_layer_32_44_0 26 cert44_layer_32_44_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.b LColor.p 26 cert44_seen_32_44_1 = cert44_component_32_44
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 32 []) LColor.b LColor.p
    cert44_seen_32_44_1 cert44_layer_32_44_1 25 cert44_layer_32_44_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 32 [])
      LColor.b LColor.p 25 cert44_seen_32_44_2 = cert44_component_32_44
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 32 []) LColor.b LColor.p
    cert44_seen_32_44_2 cert44_layer_32_44_2_eq 25

theorem cert44_step_32_44 :
    closedCollarIndexStepBool word fiber44 32 44 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_32_44)
    (by decide) (by decide)
    (by simpa [cert44_move_32_44] using cert44_component_32_44_eq)
    (by decide) (by decide) (by decide)

def cert44_move_33_45 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_33_45 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_33_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_33_45_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_33_45_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.b LColor.p cert44_seen_33_45_0 = cert44_layer_33_45_0 := by
  decide

def cert44_seen_33_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_33_45_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_33_45_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.b LColor.p cert44_seen_33_45_1 = cert44_layer_33_45_1 := by
  decide

def cert44_seen_33_45_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_33_45_2 : List ChainEdge :=
  []

theorem cert44_layer_33_45_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 33 [])
      LColor.b LColor.p cert44_seen_33_45_2 = cert44_layer_33_45_2 := by
  decide

theorem cert44_component_33_45_eq :
    closedCollarComponent word (listGetD fiber44 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_33_45 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 33 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.b LColor.p 27 cert44_seen_33_45_0 = cert44_component_33_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 33 []) LColor.b LColor.p
    cert44_seen_33_45_0 cert44_layer_33_45_0 26 cert44_layer_33_45_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.b LColor.p 26 cert44_seen_33_45_1 = cert44_component_33_45
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 33 []) LColor.b LColor.p
    cert44_seen_33_45_1 cert44_layer_33_45_1 25 cert44_layer_33_45_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 33 [])
      LColor.b LColor.p 25 cert44_seen_33_45_2 = cert44_component_33_45
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 33 []) LColor.b LColor.p
    cert44_seen_33_45_2 cert44_layer_33_45_2_eq 25

theorem cert44_step_33_45 :
    closedCollarIndexStepBool word fiber44 33 45 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_33_45)
    (by decide) (by decide)
    (by simpa [cert44_move_33_45] using cert44_component_33_45_eq)
    (by decide) (by decide) (by decide)

def cert44_move_34_46 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_34_46 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_34_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_34_46_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_34_46_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.b LColor.p cert44_seen_34_46_0 = cert44_layer_34_46_0 := by
  decide

def cert44_seen_34_46_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_34_46_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_34_46_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.b LColor.p cert44_seen_34_46_1 = cert44_layer_34_46_1 := by
  decide

def cert44_seen_34_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_34_46_2 : List ChainEdge :=
  []

theorem cert44_layer_34_46_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 34 [])
      LColor.b LColor.p cert44_seen_34_46_2 = cert44_layer_34_46_2 := by
  decide

theorem cert44_component_34_46_eq :
    closedCollarComponent word (listGetD fiber44 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_34_46 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 34 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.b LColor.p 27 cert44_seen_34_46_0 = cert44_component_34_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 34 []) LColor.b LColor.p
    cert44_seen_34_46_0 cert44_layer_34_46_0 26 cert44_layer_34_46_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.b LColor.p 26 cert44_seen_34_46_1 = cert44_component_34_46
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 34 []) LColor.b LColor.p
    cert44_seen_34_46_1 cert44_layer_34_46_1 25 cert44_layer_34_46_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 34 [])
      LColor.b LColor.p 25 cert44_seen_34_46_2 = cert44_component_34_46
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 34 []) LColor.b LColor.p
    cert44_seen_34_46_2 cert44_layer_34_46_2_eq 25

theorem cert44_step_34_46 :
    closedCollarIndexStepBool word fiber44 34 46 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_34_46)
    (by decide) (by decide)
    (by simpa [cert44_move_34_46] using cert44_component_34_46_eq)
    (by decide) (by decide) (by decide)

def cert44_move_35_47 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_35_47 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_35_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_35_47_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_35_47_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.b LColor.p cert44_seen_35_47_0 = cert44_layer_35_47_0 := by
  decide

def cert44_seen_35_47_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_35_47_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_35_47_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.b LColor.p cert44_seen_35_47_1 = cert44_layer_35_47_1 := by
  decide

def cert44_seen_35_47_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_35_47_2 : List ChainEdge :=
  []

theorem cert44_layer_35_47_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 35 [])
      LColor.b LColor.p cert44_seen_35_47_2 = cert44_layer_35_47_2 := by
  decide

theorem cert44_component_35_47_eq :
    closedCollarComponent word (listGetD fiber44 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_35_47 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 35 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.b LColor.p 27 cert44_seen_35_47_0 = cert44_component_35_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 35 []) LColor.b LColor.p
    cert44_seen_35_47_0 cert44_layer_35_47_0 26 cert44_layer_35_47_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.b LColor.p 26 cert44_seen_35_47_1 = cert44_component_35_47
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 35 []) LColor.b LColor.p
    cert44_seen_35_47_1 cert44_layer_35_47_1 25 cert44_layer_35_47_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 35 [])
      LColor.b LColor.p 25 cert44_seen_35_47_2 = cert44_component_35_47
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 35 []) LColor.b LColor.p
    cert44_seen_35_47_2 cert44_layer_35_47_2_eq 25

theorem cert44_step_35_47 :
    closedCollarIndexStepBool word fiber44 35 47 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_35_47)
    (by decide) (by decide)
    (by simpa [cert44_move_35_47] using cert44_component_35_47_eq)
    (by decide) (by decide) (by decide)

def cert44_move_36_10 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_36_10 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_36_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_36_10_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_36_10_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_0 = cert44_layer_36_10_0 := by
  decide

def cert44_seen_36_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_36_10_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_36_10_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_1 = cert44_layer_36_10_1 := by
  decide

def cert44_seen_36_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_36_10_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_36_10_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_2 = cert44_layer_36_10_2 := by
  decide

def cert44_seen_36_10_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_36_10_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_36_10_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_3 = cert44_layer_36_10_3 := by
  decide

def cert44_seen_36_10_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_36_10_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_36_10_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_4 = cert44_layer_36_10_4 := by
  decide

def cert44_seen_36_10_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_36_10_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_36_10_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_5 = cert44_layer_36_10_5 := by
  decide

def cert44_seen_36_10_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_36_10_6 : List ChainEdge :=
  []

theorem cert44_layer_36_10_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 36 [])
      LColor.r LColor.p cert44_seen_36_10_6 = cert44_layer_36_10_6 := by
  decide

theorem cert44_component_36_10_eq :
    closedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_36_10 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 36 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 27 cert44_seen_36_10_0 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_0 cert44_layer_36_10_0 26 cert44_layer_36_10_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 26 cert44_seen_36_10_1 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_1 cert44_layer_36_10_1 25 cert44_layer_36_10_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 25 cert44_seen_36_10_2 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_2 cert44_layer_36_10_2 24 cert44_layer_36_10_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 24 cert44_seen_36_10_3 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_3 cert44_layer_36_10_3 23 cert44_layer_36_10_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 23 cert44_seen_36_10_4 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_4 cert44_layer_36_10_4 22 cert44_layer_36_10_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 22 cert44_seen_36_10_5 = cert44_component_36_10
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_5 cert44_layer_36_10_5 21 cert44_layer_36_10_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 36 [])
      LColor.r LColor.p 21 cert44_seen_36_10_6 = cert44_component_36_10
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 36 []) LColor.r LColor.p
    cert44_seen_36_10_6 cert44_layer_36_10_6_eq 21

theorem cert44_step_36_10 :
    closedCollarIndexStepBool word fiber44 36 10 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_36_10)
    (by decide) (by decide)
    (by simpa [cert44_move_36_10] using cert44_component_36_10_eq)
    (by decide) (by decide) (by decide)

def cert44_move_37_11 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_37_11 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_37_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_37_11_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_37_11_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_0 = cert44_layer_37_11_0 := by
  decide

def cert44_seen_37_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_37_11_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_37_11_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_1 = cert44_layer_37_11_1 := by
  decide

def cert44_seen_37_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_37_11_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_37_11_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_2 = cert44_layer_37_11_2 := by
  decide

def cert44_seen_37_11_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_37_11_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_37_11_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_3 = cert44_layer_37_11_3 := by
  decide

def cert44_seen_37_11_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_37_11_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_37_11_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_4 = cert44_layer_37_11_4 := by
  decide

def cert44_seen_37_11_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_37_11_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_37_11_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_5 = cert44_layer_37_11_5 := by
  decide

def cert44_seen_37_11_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B5 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_37_11_6 : List ChainEdge :=
  []

theorem cert44_layer_37_11_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 37 [])
      LColor.r LColor.p cert44_seen_37_11_6 = cert44_layer_37_11_6 := by
  decide

theorem cert44_component_37_11_eq :
    closedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_37_11 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 37 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 27 cert44_seen_37_11_0 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_0 cert44_layer_37_11_0 26 cert44_layer_37_11_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 26 cert44_seen_37_11_1 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_1 cert44_layer_37_11_1 25 cert44_layer_37_11_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 25 cert44_seen_37_11_2 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_2 cert44_layer_37_11_2 24 cert44_layer_37_11_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 24 cert44_seen_37_11_3 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_3 cert44_layer_37_11_3 23 cert44_layer_37_11_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 23 cert44_seen_37_11_4 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_4 cert44_layer_37_11_4 22 cert44_layer_37_11_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 22 cert44_seen_37_11_5 = cert44_component_37_11
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_5 cert44_layer_37_11_5 21 cert44_layer_37_11_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 37 [])
      LColor.r LColor.p 21 cert44_seen_37_11_6 = cert44_component_37_11
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 37 []) LColor.r LColor.p
    cert44_seen_37_11_6 cert44_layer_37_11_6_eq 21

theorem cert44_step_37_11 :
    closedCollarIndexStepBool word fiber44 37 11 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_37_11)
    (by decide) (by decide)
    (by simpa [cert44_move_37_11] using cert44_component_37_11_eq)
    (by decide) (by decide) (by decide)

def cert44_move_38_6 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_38_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_38_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_38_6_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_38_6_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.r LColor.p cert44_seen_38_6_0 = cert44_layer_38_6_0 := by
  decide

def cert44_seen_38_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_38_6_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_38_6_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.r LColor.p cert44_seen_38_6_1 = cert44_layer_38_6_1 := by
  decide

def cert44_seen_38_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_38_6_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_38_6_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.r LColor.p cert44_seen_38_6_2 = cert44_layer_38_6_2 := by
  decide

def cert44_seen_38_6_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_38_6_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_38_6_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.r LColor.p cert44_seen_38_6_3 = cert44_layer_38_6_3 := by
  decide

def cert44_seen_38_6_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_38_6_4 : List ChainEdge :=
  []

theorem cert44_layer_38_6_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 38 [])
      LColor.r LColor.p cert44_seen_38_6_4 = cert44_layer_38_6_4 := by
  decide

theorem cert44_component_38_6_eq :
    closedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_38_6 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 38 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p 27 cert44_seen_38_6_0 = cert44_component_38_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.r LColor.p
    cert44_seen_38_6_0 cert44_layer_38_6_0 26 cert44_layer_38_6_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p 26 cert44_seen_38_6_1 = cert44_component_38_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.r LColor.p
    cert44_seen_38_6_1 cert44_layer_38_6_1 25 cert44_layer_38_6_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p 25 cert44_seen_38_6_2 = cert44_component_38_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.r LColor.p
    cert44_seen_38_6_2 cert44_layer_38_6_2 24 cert44_layer_38_6_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p 24 cert44_seen_38_6_3 = cert44_component_38_6
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 38 []) LColor.r LColor.p
    cert44_seen_38_6_3 cert44_layer_38_6_3 23 cert44_layer_38_6_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 38 [])
      LColor.r LColor.p 23 cert44_seen_38_6_4 = cert44_component_38_6
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 38 []) LColor.r LColor.p
    cert44_seen_38_6_4 cert44_layer_38_6_4_eq 23

theorem cert44_step_38_6 :
    closedCollarIndexStepBool word fiber44 38 6 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_38_6)
    (by decide) (by decide)
    (by simpa [cert44_move_38_6] using cert44_component_38_6_eq)
    (by decide) (by decide) (by decide)

def cert44_move_39_7 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_39_7 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_39_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_39_7_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_39_7_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.r LColor.p cert44_seen_39_7_0 = cert44_layer_39_7_0 := by
  decide

def cert44_seen_39_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_39_7_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_39_7_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.r LColor.p cert44_seen_39_7_1 = cert44_layer_39_7_1 := by
  decide

def cert44_seen_39_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_39_7_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_39_7_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.r LColor.p cert44_seen_39_7_2 = cert44_layer_39_7_2 := by
  decide

def cert44_seen_39_7_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_39_7_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_39_7_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.r LColor.p cert44_seen_39_7_3 = cert44_layer_39_7_3 := by
  decide

def cert44_seen_39_7_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_39_7_4 : List ChainEdge :=
  []

theorem cert44_layer_39_7_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 39 [])
      LColor.r LColor.p cert44_seen_39_7_4 = cert44_layer_39_7_4 := by
  decide

theorem cert44_component_39_7_eq :
    closedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_39_7 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 39 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p 27 cert44_seen_39_7_0 = cert44_component_39_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.r LColor.p
    cert44_seen_39_7_0 cert44_layer_39_7_0 26 cert44_layer_39_7_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p 26 cert44_seen_39_7_1 = cert44_component_39_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.r LColor.p
    cert44_seen_39_7_1 cert44_layer_39_7_1 25 cert44_layer_39_7_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p 25 cert44_seen_39_7_2 = cert44_component_39_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.r LColor.p
    cert44_seen_39_7_2 cert44_layer_39_7_2 24 cert44_layer_39_7_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p 24 cert44_seen_39_7_3 = cert44_component_39_7
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 39 []) LColor.r LColor.p
    cert44_seen_39_7_3 cert44_layer_39_7_3 23 cert44_layer_39_7_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 39 [])
      LColor.r LColor.p 23 cert44_seen_39_7_4 = cert44_component_39_7
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 39 []) LColor.r LColor.p
    cert44_seen_39_7_4 cert44_layer_39_7_4_eq 23

theorem cert44_step_39_7 :
    closedCollarIndexStepBool word fiber44 39 7 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_39_7)
    (by decide) (by decide)
    (by simpa [cert44_move_39_7] using cert44_component_39_7_eq)
    (by decide) (by decide) (by decide)

def cert44_move_40_8 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_40_8 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_40_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_40_8_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_40_8_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.p cert44_seen_40_8_0 = cert44_layer_40_8_0 := by
  decide

def cert44_seen_40_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_40_8_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_40_8_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.p cert44_seen_40_8_1 = cert44_layer_40_8_1 := by
  decide

def cert44_seen_40_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_40_8_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_40_8_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.p cert44_seen_40_8_2 = cert44_layer_40_8_2 := by
  decide

def cert44_seen_40_8_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_40_8_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_40_8_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.p cert44_seen_40_8_3 = cert44_layer_40_8_3 := by
  decide

def cert44_seen_40_8_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_40_8_4 : List ChainEdge :=
  []

theorem cert44_layer_40_8_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 40 [])
      LColor.r LColor.p cert44_seen_40_8_4 = cert44_layer_40_8_4 := by
  decide

theorem cert44_component_40_8_eq :
    closedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_40_8 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 40 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p 27 cert44_seen_40_8_0 = cert44_component_40_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.p
    cert44_seen_40_8_0 cert44_layer_40_8_0 26 cert44_layer_40_8_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p 26 cert44_seen_40_8_1 = cert44_component_40_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.p
    cert44_seen_40_8_1 cert44_layer_40_8_1 25 cert44_layer_40_8_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p 25 cert44_seen_40_8_2 = cert44_component_40_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.p
    cert44_seen_40_8_2 cert44_layer_40_8_2 24 cert44_layer_40_8_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p 24 cert44_seen_40_8_3 = cert44_component_40_8
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 40 []) LColor.r LColor.p
    cert44_seen_40_8_3 cert44_layer_40_8_3 23 cert44_layer_40_8_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 40 [])
      LColor.r LColor.p 23 cert44_seen_40_8_4 = cert44_component_40_8
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 40 []) LColor.r LColor.p
    cert44_seen_40_8_4 cert44_layer_40_8_4_eq 23

theorem cert44_step_40_8 :
    closedCollarIndexStepBool word fiber44 40 8 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_40_8)
    (by decide) (by decide)
    (by simpa [cert44_move_40_8] using cert44_component_40_8_eq)
    (by decide) (by decide) (by decide)

def cert44_move_41_9 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_41_9 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_41_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_41_9_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_41_9_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.p cert44_seen_41_9_0 = cert44_layer_41_9_0 := by
  decide

def cert44_seen_41_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_41_9_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_41_9_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.p cert44_seen_41_9_1 = cert44_layer_41_9_1 := by
  decide

def cert44_seen_41_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_41_9_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_41_9_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.p cert44_seen_41_9_2 = cert44_layer_41_9_2 := by
  decide

def cert44_seen_41_9_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_41_9_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_41_9_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.p cert44_seen_41_9_3 = cert44_layer_41_9_3 := by
  decide

def cert44_seen_41_9_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B5 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_41_9_4 : List ChainEdge :=
  []

theorem cert44_layer_41_9_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 41 [])
      LColor.r LColor.p cert44_seen_41_9_4 = cert44_layer_41_9_4 := by
  decide

theorem cert44_component_41_9_eq :
    closedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_41_9 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 41 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p 27 cert44_seen_41_9_0 = cert44_component_41_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.p
    cert44_seen_41_9_0 cert44_layer_41_9_0 26 cert44_layer_41_9_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p 26 cert44_seen_41_9_1 = cert44_component_41_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.p
    cert44_seen_41_9_1 cert44_layer_41_9_1 25 cert44_layer_41_9_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p 25 cert44_seen_41_9_2 = cert44_component_41_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.p
    cert44_seen_41_9_2 cert44_layer_41_9_2 24 cert44_layer_41_9_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p 24 cert44_seen_41_9_3 = cert44_component_41_9
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 41 []) LColor.r LColor.p
    cert44_seen_41_9_3 cert44_layer_41_9_3 23 cert44_layer_41_9_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 41 [])
      LColor.r LColor.p 23 cert44_seen_41_9_4 = cert44_component_41_9
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 41 []) LColor.r LColor.p
    cert44_seen_41_9_4 cert44_layer_41_9_4_eq 23

theorem cert44_step_41_9 :
    closedCollarIndexStepBool word fiber44 41 9 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_41_9)
    (by decide) (by decide)
    (by simpa [cert44_move_41_9] using cert44_component_41_9_eq)
    (by decide) (by decide) (by decide)

def cert44_move_42_4 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_42_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_42_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_42_4_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_42_4_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_0 = cert44_layer_42_4_0 := by
  decide

def cert44_seen_42_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_42_4_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_42_4_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_1 = cert44_layer_42_4_1 := by
  decide

def cert44_seen_42_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_42_4_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_42_4_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_2 = cert44_layer_42_4_2 := by
  decide

def cert44_seen_42_4_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_42_4_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_42_4_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_3 = cert44_layer_42_4_3 := by
  decide

def cert44_seen_42_4_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_42_4_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_42_4_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_4 = cert44_layer_42_4_4 := by
  decide

def cert44_seen_42_4_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_42_4_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_42_4_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_5 = cert44_layer_42_4_5 := by
  decide

def cert44_seen_42_4_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_42_4_6 : List ChainEdge :=
  []

theorem cert44_layer_42_4_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.r LColor.p cert44_seen_42_4_6 = cert44_layer_42_4_6 := by
  decide

theorem cert44_component_42_4_eq :
    closedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_42_4 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 42 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 27 cert44_seen_42_4_0 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_0 cert44_layer_42_4_0 26 cert44_layer_42_4_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 26 cert44_seen_42_4_1 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_1 cert44_layer_42_4_1 25 cert44_layer_42_4_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 25 cert44_seen_42_4_2 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_2 cert44_layer_42_4_2 24 cert44_layer_42_4_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 24 cert44_seen_42_4_3 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_3 cert44_layer_42_4_3 23 cert44_layer_42_4_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 23 cert44_seen_42_4_4 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_4 cert44_layer_42_4_4 22 cert44_layer_42_4_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 22 cert44_seen_42_4_5 = cert44_component_42_4
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_5 cert44_layer_42_4_5 21 cert44_layer_42_4_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.r LColor.p 21 cert44_seen_42_4_6 = cert44_component_42_4
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 42 []) LColor.r LColor.p
    cert44_seen_42_4_6 cert44_layer_42_4_6_eq 21

theorem cert44_step_42_4 :
    closedCollarIndexStepBool word fiber44 42 4 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_42_4)
    (by decide) (by decide)
    (by simpa [cert44_move_42_4] using cert44_component_42_4_eq)
    (by decide) (by decide) (by decide)

def cert44_move_42_30 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_42_30 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_42_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_42_30_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_42_30_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.b LColor.p cert44_seen_42_30_0 = cert44_layer_42_30_0 := by
  decide

def cert44_seen_42_30_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_42_30_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_42_30_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.b LColor.p cert44_seen_42_30_1 = cert44_layer_42_30_1 := by
  decide

def cert44_seen_42_30_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_42_30_2 : List ChainEdge :=
  []

theorem cert44_layer_42_30_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 42 [])
      LColor.b LColor.p cert44_seen_42_30_2 = cert44_layer_42_30_2 := by
  decide

theorem cert44_component_42_30_eq :
    closedCollarComponent word (listGetD fiber44 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_42_30 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 42 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.b LColor.p 27 cert44_seen_42_30_0 = cert44_component_42_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.b LColor.p
    cert44_seen_42_30_0 cert44_layer_42_30_0 26 cert44_layer_42_30_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.b LColor.p 26 cert44_seen_42_30_1 = cert44_component_42_30
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 42 []) LColor.b LColor.p
    cert44_seen_42_30_1 cert44_layer_42_30_1 25 cert44_layer_42_30_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 42 [])
      LColor.b LColor.p 25 cert44_seen_42_30_2 = cert44_component_42_30
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 42 []) LColor.b LColor.p
    cert44_seen_42_30_2 cert44_layer_42_30_2_eq 25

theorem cert44_step_42_30 :
    closedCollarIndexStepBool word fiber44 42 30 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_42_30)
    (by decide) (by decide)
    (by simpa [cert44_move_42_30] using cert44_component_42_30_eq)
    (by decide) (by decide) (by decide)

def cert44_move_43_5 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_43_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_seen_43_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_43_5_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_43_5_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_0 = cert44_layer_43_5_0 := by
  decide

def cert44_seen_43_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_43_5_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

theorem cert44_layer_43_5_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_1 = cert44_layer_43_5_1 := by
  decide

def cert44_seen_43_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }]

def cert44_layer_43_5_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

theorem cert44_layer_43_5_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_2 = cert44_layer_43_5_2 := by
  decide

def cert44_seen_43_5_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }]

def cert44_layer_43_5_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

theorem cert44_layer_43_5_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_3 = cert44_layer_43_5_3 := by
  decide

def cert44_seen_43_5_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }]

def cert44_layer_43_5_4 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

theorem cert44_layer_43_5_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_4 = cert44_layer_43_5_4 := by
  decide

def cert44_seen_43_5_5 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }]

def cert44_layer_43_5_5 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F2F4 }]

theorem cert44_layer_43_5_5_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_5 = cert44_layer_43_5_5 := by
  decide

def cert44_seen_43_5_6 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.B6 }, { occ := 2, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }, { occ := 2, edge := TauEdge.F2F3 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F2F4 }]

def cert44_layer_43_5_6 : List ChainEdge :=
  []

theorem cert44_layer_43_5_6_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.r LColor.p cert44_seen_43_5_6 = cert44_layer_43_5_6 := by
  decide

theorem cert44_component_43_5_eq :
    closedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_43_5 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 43 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 27 cert44_seen_43_5_0 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_0 cert44_layer_43_5_0 26 cert44_layer_43_5_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 26 cert44_seen_43_5_1 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_1 cert44_layer_43_5_1 25 cert44_layer_43_5_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 25 cert44_seen_43_5_2 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_2 cert44_layer_43_5_2 24 cert44_layer_43_5_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 24 cert44_seen_43_5_3 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_3 cert44_layer_43_5_3 23 cert44_layer_43_5_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 23 cert44_seen_43_5_4 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_4 cert44_layer_43_5_4 22 cert44_layer_43_5_4_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 22 cert44_seen_43_5_5 = cert44_component_43_5
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_5 cert44_layer_43_5_5 21 cert44_layer_43_5_5_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.r LColor.p 21 cert44_seen_43_5_6 = cert44_component_43_5
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 43 []) LColor.r LColor.p
    cert44_seen_43_5_6 cert44_layer_43_5_6_eq 21

theorem cert44_step_43_5 :
    closedCollarIndexStepBool word fiber44 43 5 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_43_5)
    (by decide) (by decide)
    (by simpa [cert44_move_43_5] using cert44_component_43_5_eq)
    (by decide) (by decide) (by decide)

def cert44_move_43_31 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_43_31 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_43_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_43_31_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_43_31_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.b LColor.p cert44_seen_43_31_0 = cert44_layer_43_31_0 := by
  decide

def cert44_seen_43_31_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_43_31_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_43_31_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.b LColor.p cert44_seen_43_31_1 = cert44_layer_43_31_1 := by
  decide

def cert44_seen_43_31_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_43_31_2 : List ChainEdge :=
  []

theorem cert44_layer_43_31_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 43 [])
      LColor.b LColor.p cert44_seen_43_31_2 = cert44_layer_43_31_2 := by
  decide

theorem cert44_component_43_31_eq :
    closedCollarComponent word (listGetD fiber44 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_43_31 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 43 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.b LColor.p 27 cert44_seen_43_31_0 = cert44_component_43_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.b LColor.p
    cert44_seen_43_31_0 cert44_layer_43_31_0 26 cert44_layer_43_31_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.b LColor.p 26 cert44_seen_43_31_1 = cert44_component_43_31
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 43 []) LColor.b LColor.p
    cert44_seen_43_31_1 cert44_layer_43_31_1 25 cert44_layer_43_31_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 43 [])
      LColor.b LColor.p 25 cert44_seen_43_31_2 = cert44_component_43_31
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 43 []) LColor.b LColor.p
    cert44_seen_43_31_2 cert44_layer_43_31_2_eq 25

theorem cert44_step_43_31 :
    closedCollarIndexStepBool word fiber44 43 31 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_43_31)
    (by decide) (by decide)
    (by simpa [cert44_move_43_31] using cert44_component_43_31_eq)
    (by decide) (by decide) (by decide)

def cert44_move_44_0 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_44_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_44_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_44_0_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_44_0_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.r LColor.p cert44_seen_44_0_0 = cert44_layer_44_0_0 := by
  decide

def cert44_seen_44_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_44_0_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_44_0_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.r LColor.p cert44_seen_44_0_1 = cert44_layer_44_0_1 := by
  decide

def cert44_seen_44_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_44_0_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_44_0_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.r LColor.p cert44_seen_44_0_2 = cert44_layer_44_0_2 := by
  decide

def cert44_seen_44_0_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_44_0_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_44_0_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.r LColor.p cert44_seen_44_0_3 = cert44_layer_44_0_3 := by
  decide

def cert44_seen_44_0_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_44_0_4 : List ChainEdge :=
  []

theorem cert44_layer_44_0_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.r LColor.p cert44_seen_44_0_4 = cert44_layer_44_0_4 := by
  decide

theorem cert44_component_44_0_eq :
    closedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_44_0 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 44 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p 27 cert44_seen_44_0_0 = cert44_component_44_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.r LColor.p
    cert44_seen_44_0_0 cert44_layer_44_0_0 26 cert44_layer_44_0_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p 26 cert44_seen_44_0_1 = cert44_component_44_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.r LColor.p
    cert44_seen_44_0_1 cert44_layer_44_0_1 25 cert44_layer_44_0_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p 25 cert44_seen_44_0_2 = cert44_component_44_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.r LColor.p
    cert44_seen_44_0_2 cert44_layer_44_0_2 24 cert44_layer_44_0_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p 24 cert44_seen_44_0_3 = cert44_component_44_0
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.r LColor.p
    cert44_seen_44_0_3 cert44_layer_44_0_3 23 cert44_layer_44_0_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.r LColor.p 23 cert44_seen_44_0_4 = cert44_component_44_0
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 44 []) LColor.r LColor.p
    cert44_seen_44_0_4 cert44_layer_44_0_4_eq 23

theorem cert44_step_44_0 :
    closedCollarIndexStepBool word fiber44 44 0 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_44_0)
    (by decide) (by decide)
    (by simpa [cert44_move_44_0] using cert44_component_44_0_eq)
    (by decide) (by decide) (by decide)

def cert44_move_44_32 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_44_32 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_44_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_44_32_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_44_32_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.b LColor.p cert44_seen_44_32_0 = cert44_layer_44_32_0 := by
  decide

def cert44_seen_44_32_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_44_32_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_44_32_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.b LColor.p cert44_seen_44_32_1 = cert44_layer_44_32_1 := by
  decide

def cert44_seen_44_32_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_44_32_2 : List ChainEdge :=
  []

theorem cert44_layer_44_32_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 44 [])
      LColor.b LColor.p cert44_seen_44_32_2 = cert44_layer_44_32_2 := by
  decide

theorem cert44_component_44_32_eq :
    closedCollarComponent word (listGetD fiber44 44 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_44_32 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 44 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.b LColor.p 27 cert44_seen_44_32_0 = cert44_component_44_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.b LColor.p
    cert44_seen_44_32_0 cert44_layer_44_32_0 26 cert44_layer_44_32_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.b LColor.p 26 cert44_seen_44_32_1 = cert44_component_44_32
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 44 []) LColor.b LColor.p
    cert44_seen_44_32_1 cert44_layer_44_32_1 25 cert44_layer_44_32_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 44 [])
      LColor.b LColor.p 25 cert44_seen_44_32_2 = cert44_component_44_32
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 44 []) LColor.b LColor.p
    cert44_seen_44_32_2 cert44_layer_44_32_2_eq 25

theorem cert44_step_44_32 :
    closedCollarIndexStepBool word fiber44 44 32 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_44_32)
    (by decide) (by decide)
    (by simpa [cert44_move_44_32] using cert44_component_44_32_eq)
    (by decide) (by decide) (by decide)

def cert44_move_45_1 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_45_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_45_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_45_1_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_45_1_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.r LColor.p cert44_seen_45_1_0 = cert44_layer_45_1_0 := by
  decide

def cert44_seen_45_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_45_1_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_45_1_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.r LColor.p cert44_seen_45_1_1 = cert44_layer_45_1_1 := by
  decide

def cert44_seen_45_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_45_1_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_45_1_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.r LColor.p cert44_seen_45_1_2 = cert44_layer_45_1_2 := by
  decide

def cert44_seen_45_1_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_45_1_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_45_1_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.r LColor.p cert44_seen_45_1_3 = cert44_layer_45_1_3 := by
  decide

def cert44_seen_45_1_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_45_1_4 : List ChainEdge :=
  []

theorem cert44_layer_45_1_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.r LColor.p cert44_seen_45_1_4 = cert44_layer_45_1_4 := by
  decide

theorem cert44_component_45_1_eq :
    closedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_45_1 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 45 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p 27 cert44_seen_45_1_0 = cert44_component_45_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.r LColor.p
    cert44_seen_45_1_0 cert44_layer_45_1_0 26 cert44_layer_45_1_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p 26 cert44_seen_45_1_1 = cert44_component_45_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.r LColor.p
    cert44_seen_45_1_1 cert44_layer_45_1_1 25 cert44_layer_45_1_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p 25 cert44_seen_45_1_2 = cert44_component_45_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.r LColor.p
    cert44_seen_45_1_2 cert44_layer_45_1_2 24 cert44_layer_45_1_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p 24 cert44_seen_45_1_3 = cert44_component_45_1
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.r LColor.p
    cert44_seen_45_1_3 cert44_layer_45_1_3 23 cert44_layer_45_1_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.r LColor.p 23 cert44_seen_45_1_4 = cert44_component_45_1
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 45 []) LColor.r LColor.p
    cert44_seen_45_1_4 cert44_layer_45_1_4_eq 23

theorem cert44_step_45_1 :
    closedCollarIndexStepBool word fiber44 45 1 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_45_1)
    (by decide) (by decide)
    (by simpa [cert44_move_45_1] using cert44_component_45_1_eq)
    (by decide) (by decide) (by decide)

def cert44_move_45_33 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_45_33 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_45_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_45_33_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_45_33_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.b LColor.p cert44_seen_45_33_0 = cert44_layer_45_33_0 := by
  decide

def cert44_seen_45_33_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_45_33_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_45_33_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.b LColor.p cert44_seen_45_33_1 = cert44_layer_45_33_1 := by
  decide

def cert44_seen_45_33_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_45_33_2 : List ChainEdge :=
  []

theorem cert44_layer_45_33_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 45 [])
      LColor.b LColor.p cert44_seen_45_33_2 = cert44_layer_45_33_2 := by
  decide

theorem cert44_component_45_33_eq :
    closedCollarComponent word (listGetD fiber44 45 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_45_33 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 45 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.b LColor.p 27 cert44_seen_45_33_0 = cert44_component_45_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.b LColor.p
    cert44_seen_45_33_0 cert44_layer_45_33_0 26 cert44_layer_45_33_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.b LColor.p 26 cert44_seen_45_33_1 = cert44_component_45_33
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 45 []) LColor.b LColor.p
    cert44_seen_45_33_1 cert44_layer_45_33_1 25 cert44_layer_45_33_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 45 [])
      LColor.b LColor.p 25 cert44_seen_45_33_2 = cert44_component_45_33
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 45 []) LColor.b LColor.p
    cert44_seen_45_33_2 cert44_layer_45_33_2_eq 25

theorem cert44_step_45_33 :
    closedCollarIndexStepBool word fiber44 45 33 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_45_33)
    (by decide) (by decide)
    (by simpa [cert44_move_45_33] using cert44_component_45_33_eq)
    (by decide) (by decide) (by decide)

def cert44_move_46_2 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_46_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_46_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_46_2_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_46_2_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.r LColor.p cert44_seen_46_2_0 = cert44_layer_46_2_0 := by
  decide

def cert44_seen_46_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_46_2_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_46_2_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.r LColor.p cert44_seen_46_2_1 = cert44_layer_46_2_1 := by
  decide

def cert44_seen_46_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_46_2_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_46_2_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.r LColor.p cert44_seen_46_2_2 = cert44_layer_46_2_2 := by
  decide

def cert44_seen_46_2_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_46_2_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_46_2_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.r LColor.p cert44_seen_46_2_3 = cert44_layer_46_2_3 := by
  decide

def cert44_seen_46_2_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_46_2_4 : List ChainEdge :=
  []

theorem cert44_layer_46_2_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.r LColor.p cert44_seen_46_2_4 = cert44_layer_46_2_4 := by
  decide

theorem cert44_component_46_2_eq :
    closedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_46_2 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 46 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p 27 cert44_seen_46_2_0 = cert44_component_46_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.r LColor.p
    cert44_seen_46_2_0 cert44_layer_46_2_0 26 cert44_layer_46_2_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p 26 cert44_seen_46_2_1 = cert44_component_46_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.r LColor.p
    cert44_seen_46_2_1 cert44_layer_46_2_1 25 cert44_layer_46_2_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p 25 cert44_seen_46_2_2 = cert44_component_46_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.r LColor.p
    cert44_seen_46_2_2 cert44_layer_46_2_2 24 cert44_layer_46_2_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p 24 cert44_seen_46_2_3 = cert44_component_46_2
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.r LColor.p
    cert44_seen_46_2_3 cert44_layer_46_2_3 23 cert44_layer_46_2_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.r LColor.p 23 cert44_seen_46_2_4 = cert44_component_46_2
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 46 []) LColor.r LColor.p
    cert44_seen_46_2_4 cert44_layer_46_2_4_eq 23

theorem cert44_step_46_2 :
    closedCollarIndexStepBool word fiber44 46 2 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_46_2)
    (by decide) (by decide)
    (by simpa [cert44_move_46_2] using cert44_component_46_2_eq)
    (by decide) (by decide) (by decide)

def cert44_move_46_34 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_46_34 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_46_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_46_34_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_46_34_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.b LColor.p cert44_seen_46_34_0 = cert44_layer_46_34_0 := by
  decide

def cert44_seen_46_34_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_46_34_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_46_34_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.b LColor.p cert44_seen_46_34_1 = cert44_layer_46_34_1 := by
  decide

def cert44_seen_46_34_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_46_34_2 : List ChainEdge :=
  []

theorem cert44_layer_46_34_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 46 [])
      LColor.b LColor.p cert44_seen_46_34_2 = cert44_layer_46_34_2 := by
  decide

theorem cert44_component_46_34_eq :
    closedCollarComponent word (listGetD fiber44 46 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_46_34 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 46 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.b LColor.p 27 cert44_seen_46_34_0 = cert44_component_46_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.b LColor.p
    cert44_seen_46_34_0 cert44_layer_46_34_0 26 cert44_layer_46_34_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.b LColor.p 26 cert44_seen_46_34_1 = cert44_component_46_34
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 46 []) LColor.b LColor.p
    cert44_seen_46_34_1 cert44_layer_46_34_1 25 cert44_layer_46_34_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 46 [])
      LColor.b LColor.p 25 cert44_seen_46_34_2 = cert44_component_46_34
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 46 []) LColor.b LColor.p
    cert44_seen_46_34_2 cert44_layer_46_34_2_eq 25

theorem cert44_step_46_34 :
    closedCollarIndexStepBool word fiber44 46 34 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_46_34)
    (by decide) (by decide)
    (by simpa [cert44_move_46_34] using cert44_component_46_34_eq)
    (by decide) (by decide) (by decide)

def cert44_move_47_3 : ChainMove :=
  { a := LColor.r, c := LColor.p, seed := { occ := 0, edge := TauEdge.F2F3 } }

def cert44_component_47_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_47_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }]

def cert44_layer_47_3_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

theorem cert44_layer_47_3_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.r LColor.p cert44_seen_47_3_0 = cert44_layer_47_3_0 := by
  decide

def cert44_seen_47_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }]

def cert44_layer_47_3_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

theorem cert44_layer_47_3_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.r LColor.p cert44_seen_47_3_1 = cert44_layer_47_3_1 := by
  decide

def cert44_seen_47_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }]

def cert44_layer_47_3_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

theorem cert44_layer_47_3_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.r LColor.p cert44_seen_47_3_2 = cert44_layer_47_3_2 := by
  decide

def cert44_seen_47_3_3 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }]

def cert44_layer_47_3_3 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_47_3_3_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.r LColor.p cert44_seen_47_3_3 = cert44_layer_47_3_3 := by
  decide

def cert44_seen_47_3_4 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.F2F4 }, { occ := 0, edge := TauEdge.B4 }, { occ := 0, edge := TauEdge.F4F5 }, { occ := 1, edge := TauEdge.F2F3 }, { occ := 0, edge := TauEdge.B6 }, { occ := 1, edge := TauEdge.F0F2 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_47_3_4 : List ChainEdge :=
  []

theorem cert44_layer_47_3_4_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.r LColor.p cert44_seen_47_3_4 = cert44_layer_47_3_4 := by
  decide

theorem cert44_component_47_3_eq :
    closedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = cert44_component_47_3 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 47 [])
      LColor.r LColor.p { occ := 0, edge := TauEdge.F2F3 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p 27 cert44_seen_47_3_0 = cert44_component_47_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.r LColor.p
    cert44_seen_47_3_0 cert44_layer_47_3_0 26 cert44_layer_47_3_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p 26 cert44_seen_47_3_1 = cert44_component_47_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.r LColor.p
    cert44_seen_47_3_1 cert44_layer_47_3_1 25 cert44_layer_47_3_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p 25 cert44_seen_47_3_2 = cert44_component_47_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.r LColor.p
    cert44_seen_47_3_2 cert44_layer_47_3_2 24 cert44_layer_47_3_2_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p 24 cert44_seen_47_3_3 = cert44_component_47_3
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.r LColor.p
    cert44_seen_47_3_3 cert44_layer_47_3_3 23 cert44_layer_47_3_3_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.r LColor.p 23 cert44_seen_47_3_4 = cert44_component_47_3
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 47 []) LColor.r LColor.p
    cert44_seen_47_3_4 cert44_layer_47_3_4_eq 23

theorem cert44_step_47_3 :
    closedCollarIndexStepBool word fiber44 47 3 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_47_3)
    (by decide) (by decide)
    (by simpa [cert44_move_47_3] using cert44_component_47_3_eq)
    (by decide) (by decide) (by decide)

def cert44_move_47_35 : ChainMove :=
  { a := LColor.b, c := LColor.p, seed := { occ := 0, edge := TauEdge.F4F5 } }

def cert44_component_47_35 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_seen_47_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }]

def cert44_layer_47_35_0 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

theorem cert44_layer_47_35_0_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.b LColor.p cert44_seen_47_35_0 = cert44_layer_47_35_0 := by
  decide

def cert44_seen_47_35_1 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }]

def cert44_layer_47_35_1 : List ChainEdge :=
  [{ occ := 1, edge := TauEdge.F1F0 }]

theorem cert44_layer_47_35_1_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.b LColor.p cert44_seen_47_35_1 = cert44_layer_47_35_1 := by
  decide

def cert44_seen_47_35_2 : List ChainEdge :=
  [{ occ := 0, edge := TauEdge.F4F5 }, { occ := 0, edge := TauEdge.B5 }, { occ := 0, edge := TauEdge.B7 }, { occ := 1, edge := TauEdge.F1F0 }]

def cert44_layer_47_35_2 : List ChainEdge :=
  []

theorem cert44_layer_47_35_2_eq :
    closedCollarComponentLayer word (listGetD fiber44 47 [])
      LColor.b LColor.p cert44_seen_47_35_2 = cert44_layer_47_35_2 := by
  decide

theorem cert44_component_47_35_eq :
    closedCollarComponent word (listGetD fiber44 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = cert44_component_47_35 := by
  unfold closedCollarComponent
  have hseedColor : chainEdgeInPair (listGetD fiber44 47 [])
      LColor.b LColor.p { occ := 0, edge := TauEdge.F4F5 } = true := by
    decide
  simp [hseedColor]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.b LColor.p 27 cert44_seen_47_35_0 = cert44_component_47_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.b LColor.p
    cert44_seen_47_35_0 cert44_layer_47_35_0 26 cert44_layer_47_35_0_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.b LColor.p 26 cert44_seen_47_35_1 = cert44_component_47_35
  rw [closeClosedCollarComponent_succ_eq word
    (listGetD fiber44 47 []) LColor.b LColor.p
    cert44_seen_47_35_1 cert44_layer_47_35_1 25 cert44_layer_47_35_1_eq]
  change closeClosedCollarComponent word (listGetD fiber44 47 [])
      LColor.b LColor.p 25 cert44_seen_47_35_2 = cert44_component_47_35
  exact closeClosedCollarComponent_eq_self_of_layer_nil word
    (listGetD fiber44 47 []) LColor.b LColor.p
    cert44_seen_47_35_2 cert44_layer_47_35_2_eq 25

theorem cert44_step_47_35 :
    closedCollarIndexStepBool word fiber44 47 35 = true :=
  closedCollarIndexStepBool_of_component (move := cert44_move_47_35)
    (by decide) (by decide)
    (by simpa [cert44_move_47_35] using cert44_component_47_35_eq)
    (by decide) (by decide) (by decide)

theorem cert44_row_0 :
    closedCollarParentIndexValid word fiber44 cert44.parents 0 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length]

theorem cert44_row_1 :
    closedCollarParentIndexValid word fiber44 cert44.parents 1 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_1_0, cert44_step_0_1]

theorem cert44_row_2 :
    closedCollarParentIndexValid word fiber44 cert44.parents 2 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_2_1, cert44_step_1_2]

theorem cert44_row_3 :
    closedCollarParentIndexValid word fiber44 cert44.parents 3 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_3_0, cert44_step_0_3]

theorem cert44_row_4 :
    closedCollarParentIndexValid word fiber44 cert44.parents 4 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_4_0, cert44_step_0_4]

theorem cert44_row_5 :
    closedCollarParentIndexValid word fiber44 cert44.parents 5 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_5_1, cert44_step_1_5]

theorem cert44_row_6 :
    closedCollarParentIndexValid word fiber44 cert44.parents 6 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_6_0, cert44_step_0_6]

theorem cert44_row_7 :
    closedCollarParentIndexValid word fiber44 cert44.parents 7 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_7_1, cert44_step_1_7]

theorem cert44_row_8 :
    closedCollarParentIndexValid word fiber44 cert44.parents 8 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_8_2, cert44_step_2_8]

theorem cert44_row_9 :
    closedCollarParentIndexValid word fiber44 cert44.parents 9 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_9_3, cert44_step_3_9]

theorem cert44_row_10 :
    closedCollarParentIndexValid word fiber44 cert44.parents 10 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_10_4, cert44_step_4_10]

theorem cert44_row_11 :
    closedCollarParentIndexValid word fiber44 cert44.parents 11 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_11_5, cert44_step_5_11]

theorem cert44_row_12 :
    closedCollarParentIndexValid word fiber44 cert44.parents 12 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_12_0, cert44_step_0_12]

theorem cert44_row_13 :
    closedCollarParentIndexValid word fiber44 cert44.parents 13 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_13_1, cert44_step_1_13]

theorem cert44_row_14 :
    closedCollarParentIndexValid word fiber44 cert44.parents 14 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_14_2, cert44_step_2_14]

theorem cert44_row_15 :
    closedCollarParentIndexValid word fiber44 cert44.parents 15 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_15_3, cert44_step_3_15]

theorem cert44_row_16 :
    closedCollarParentIndexValid word fiber44 cert44.parents 16 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_16_4, cert44_step_4_16]

theorem cert44_row_17 :
    closedCollarParentIndexValid word fiber44 cert44.parents 17 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_17_5, cert44_step_5_17]

theorem cert44_row_18 :
    closedCollarParentIndexValid word fiber44 cert44.parents 18 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_18_6, cert44_step_6_18]

theorem cert44_row_19 :
    closedCollarParentIndexValid word fiber44 cert44.parents 19 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_19_7, cert44_step_7_19]

theorem cert44_row_20 :
    closedCollarParentIndexValid word fiber44 cert44.parents 20 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_20_8, cert44_step_8_20]

theorem cert44_row_21 :
    closedCollarParentIndexValid word fiber44 cert44.parents 21 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_21_9, cert44_step_9_21]

theorem cert44_row_22 :
    closedCollarParentIndexValid word fiber44 cert44.parents 22 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_22_10, cert44_step_10_22]

theorem cert44_row_23 :
    closedCollarParentIndexValid word fiber44 cert44.parents 23 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_23_11, cert44_step_11_23]

theorem cert44_row_24 :
    closedCollarParentIndexValid word fiber44 cert44.parents 24 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_24_16, cert44_step_16_24]

theorem cert44_row_25 :
    closedCollarParentIndexValid word fiber44 cert44.parents 25 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_25_17, cert44_step_17_25]

theorem cert44_row_26 :
    closedCollarParentIndexValid word fiber44 cert44.parents 26 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_26_12, cert44_step_12_26]

theorem cert44_row_27 :
    closedCollarParentIndexValid word fiber44 cert44.parents 27 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_27_13, cert44_step_13_27]

theorem cert44_row_28 :
    closedCollarParentIndexValid word fiber44 cert44.parents 28 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_28_14, cert44_step_14_28]

theorem cert44_row_29 :
    closedCollarParentIndexValid word fiber44 cert44.parents 29 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_29_15, cert44_step_15_29]

theorem cert44_row_30 :
    closedCollarParentIndexValid word fiber44 cert44.parents 30 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_30_42, cert44_step_42_30]

theorem cert44_row_31 :
    closedCollarParentIndexValid word fiber44 cert44.parents 31 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_31_43, cert44_step_43_31]

theorem cert44_row_32 :
    closedCollarParentIndexValid word fiber44 cert44.parents 32 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_32_44, cert44_step_44_32]

theorem cert44_row_33 :
    closedCollarParentIndexValid word fiber44 cert44.parents 33 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_33_45, cert44_step_45_33]

theorem cert44_row_34 :
    closedCollarParentIndexValid word fiber44 cert44.parents 34 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_34_46, cert44_step_46_34]

theorem cert44_row_35 :
    closedCollarParentIndexValid word fiber44 cert44.parents 35 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_35_47, cert44_step_47_35]

theorem cert44_row_36 :
    closedCollarParentIndexValid word fiber44 cert44.parents 36 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_36_10, cert44_step_10_36]

theorem cert44_row_37 :
    closedCollarParentIndexValid word fiber44 cert44.parents 37 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_37_11, cert44_step_11_37]

theorem cert44_row_38 :
    closedCollarParentIndexValid word fiber44 cert44.parents 38 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_38_6, cert44_step_6_38]

theorem cert44_row_39 :
    closedCollarParentIndexValid word fiber44 cert44.parents 39 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_39_7, cert44_step_7_39]

theorem cert44_row_40 :
    closedCollarParentIndexValid word fiber44 cert44.parents 40 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_40_8, cert44_step_8_40]

theorem cert44_row_41 :
    closedCollarParentIndexValid word fiber44 cert44.parents 41 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_41_9, cert44_step_9_41]

theorem cert44_row_42 :
    closedCollarParentIndexValid word fiber44 cert44.parents 42 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_42_4, cert44_step_4_42]

theorem cert44_row_43 :
    closedCollarParentIndexValid word fiber44 cert44.parents 43 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_43_5, cert44_step_5_43]

theorem cert44_row_44 :
    closedCollarParentIndexValid word fiber44 cert44.parents 44 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_44_0, cert44_step_0_44]

theorem cert44_row_45 :
    closedCollarParentIndexValid word fiber44 cert44.parents 45 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_45_1, cert44_step_1_45]

theorem cert44_row_46 :
    closedCollarParentIndexValid word fiber44 cert44.parents 46 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_46_2, cert44_step_2_46]

theorem cert44_row_47 :
    closedCollarParentIndexValid word fiber44 cert44.parents 47 = true := by
  have cert44_fiber_length : fiber44.length = 48 := by decide
  unfold closedCollarParentIndexValid closedCollarParentAt
  simp [cert44, listGetD, cert44_fiber_length, cert44_step_47_3, cert44_step_3_47]

theorem cert44_rows :
    closedCollarSpineRowsValid word fiber44 cert44.parents = true := by
  apply closedCollarSpineRowsValid_of_index
  intro idx hidx
  have cert44_fiber_length : fiber44.length = 48 := by decide

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
  by_cases h44 : idx = 44
  · subst idx
    exact cert44_row_44
  by_cases h45 : idx = 45
  · subst idx
    exact cert44_row_45
  by_cases h46 : idx = 46
  · subst idx
    exact cert44_row_46
  by_cases h47 : idx = 47
  · subst idx
    exact cert44_row_47
  · omega

theorem cert44_root :
    closedCollarSpineParentsReachRoot fiber44 cert44 = true := by
  decide

theorem cert44_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.p] := by
  change closedCollarFiberKempeConnected word cert44.key
  exact closedCollarFiberKempeConnected_of_spineRowsForClosedFiber cert44 fiber44_eq cert44_rows cert44_root


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
