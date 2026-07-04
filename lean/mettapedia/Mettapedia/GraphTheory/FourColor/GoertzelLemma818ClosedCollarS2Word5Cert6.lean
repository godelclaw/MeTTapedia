import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast6 : List TauState :=
  [stateAt 7, stateAt 15, stateAt 23, stateAt 31]

theorem keyedLast6_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.p, LColor.r]) =
      keyedLast6 := by
  decide

def fiber6OuterChunks : List (List (List TauState)) :=
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

def fiber6 : List (List TauState) :=
  fiber6OuterChunks.flatten

theorem fiber6_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 0 []) =
      listGetD fiber6OuterChunks 0 [] := by
  decide

theorem fiber6_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 1 []) =
      listGetD fiber6OuterChunks 1 [] := by
  decide

theorem fiber6_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 2 []) =
      listGetD fiber6OuterChunks 2 [] := by
  decide

theorem fiber6_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 3 []) =
      listGetD fiber6OuterChunks 3 [] := by
  decide

theorem fiber6_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 4 []) =
      listGetD fiber6OuterChunks 4 [] := by
  decide

theorem fiber6_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 5 []) =
      listGetD fiber6OuterChunks 5 [] := by
  decide

theorem fiber6_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 6 []) =
      listGetD fiber6OuterChunks 6 [] := by
  decide

theorem fiber6_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 7 []) =
      listGetD fiber6OuterChunks 7 [] := by
  decide

theorem fiber6_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 8 []) =
      listGetD fiber6OuterChunks 8 [] := by
  decide

theorem fiber6_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 9 []) =
      listGetD fiber6OuterChunks 9 [] := by
  decide

theorem fiber6_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 10 []) =
      listGetD fiber6OuterChunks 10 [] := by
  decide

theorem fiber6_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks 11 []) =
      listGetD fiber6OuterChunks 11 [] := by
  decide

theorem fiber6_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast6
        (listGetD tauStateChunks idx []) =
      listGetD fiber6OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber6_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber6_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber6_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber6_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber6_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber6_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber6_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber6_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber6_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber6_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber6_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber6_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber6_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast6 =
      fiber6 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast6 tauStateChunks fiber6OuterChunks
    tauStateChunks_eq (by rfl) fiber6_outer_get
  simpa [fiber6] using h

theorem fiber6_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.p, LColor.r] = fiber6 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.p, LColor.r] keyedLast6_eq
  exact hfrom.trans fiber6_keyedFrom_eq

theorem fiber6_eq :
    closedCollarFiber word [LColor.r, LColor.r, LColor.p, LColor.r] = fiber6 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.p, LColor.r]
  exact hfast.trans fiber6_keyed_eq

theorem cert6_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.p, LColor.r] = [] := by
  have hnil : fiber6 = [] := by
    decide
  exact fiber6_eq.trans hnil

theorem cert6_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert6_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
