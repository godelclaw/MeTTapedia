import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast73 : List TauState :=
  [stateAt 96, stateAt 104, stateAt 112, stateAt 120]

theorem keyedLast73_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.r, LColor.b]) =
      keyedLast73 := by
  decide

def fiber73OuterChunks : List (List (List TauState)) :=
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
, []
, []
, []
]

def fiber73 : List (List TauState) :=
  fiber73OuterChunks.flatten

theorem fiber73_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 0 []) =
      listGetD fiber73OuterChunks 0 [] := by
  decide

theorem fiber73_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 1 []) =
      listGetD fiber73OuterChunks 1 [] := by
  decide

theorem fiber73_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 2 []) =
      listGetD fiber73OuterChunks 2 [] := by
  decide

theorem fiber73_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 3 []) =
      listGetD fiber73OuterChunks 3 [] := by
  decide

theorem fiber73_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 4 []) =
      listGetD fiber73OuterChunks 4 [] := by
  decide

theorem fiber73_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 5 []) =
      listGetD fiber73OuterChunks 5 [] := by
  decide

theorem fiber73_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 6 []) =
      listGetD fiber73OuterChunks 6 [] := by
  decide

theorem fiber73_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 7 []) =
      listGetD fiber73OuterChunks 7 [] := by
  decide

theorem fiber73_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 8 []) =
      listGetD fiber73OuterChunks 8 [] := by
  decide

theorem fiber73_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 9 []) =
      listGetD fiber73OuterChunks 9 [] := by
  decide

theorem fiber73_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 10 []) =
      listGetD fiber73OuterChunks 10 [] := by
  decide

theorem fiber73_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks 11 []) =
      listGetD fiber73OuterChunks 11 [] := by
  decide

theorem fiber73_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast73
        (listGetD tauStateChunks idx []) =
      listGetD fiber73OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber73_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber73_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber73_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber73_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber73_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber73_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber73_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber73_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber73_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber73_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber73_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber73_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber73_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast73 =
      fiber73 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast73 tauStateChunks fiber73OuterChunks
    tauStateChunks_eq (by rfl) fiber73_outer_get
  simpa [fiber73] using h

theorem fiber73_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.r, LColor.b] = fiber73 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.r, LColor.b] keyedLast73_eq
  exact hfrom.trans fiber73_keyedFrom_eq

theorem fiber73_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.r, LColor.b] = fiber73 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.r, LColor.b]
  exact hfast.trans fiber73_keyed_eq

theorem cert73_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.r, LColor.b] = [] := by
  have hnil : fiber73 = [] := by
    decide
  exact fiber73_eq.trans hnil

theorem cert73_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert73_empty


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
