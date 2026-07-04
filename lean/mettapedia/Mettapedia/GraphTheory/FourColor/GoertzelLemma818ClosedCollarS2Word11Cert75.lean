import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word11

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast75 : List TauState :=
  [stateAt 36, stateAt 44, stateAt 52, stateAt 60]

theorem keyedLast75_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.b, LColor.r]) =
      keyedLast75 := by
  decide

def fiber75OuterChunks : List (List (List TauState)) :=
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

def fiber75 : List (List TauState) :=
  fiber75OuterChunks.flatten

theorem fiber75_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 0 []) =
      listGetD fiber75OuterChunks 0 [] := by
  decide

theorem fiber75_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 1 []) =
      listGetD fiber75OuterChunks 1 [] := by
  decide

theorem fiber75_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 2 []) =
      listGetD fiber75OuterChunks 2 [] := by
  decide

theorem fiber75_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 3 []) =
      listGetD fiber75OuterChunks 3 [] := by
  decide

theorem fiber75_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 4 []) =
      listGetD fiber75OuterChunks 4 [] := by
  decide

theorem fiber75_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 5 []) =
      listGetD fiber75OuterChunks 5 [] := by
  decide

theorem fiber75_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 6 []) =
      listGetD fiber75OuterChunks 6 [] := by
  decide

theorem fiber75_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 7 []) =
      listGetD fiber75OuterChunks 7 [] := by
  decide

theorem fiber75_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 8 []) =
      listGetD fiber75OuterChunks 8 [] := by
  decide

theorem fiber75_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 9 []) =
      listGetD fiber75OuterChunks 9 [] := by
  decide

theorem fiber75_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 10 []) =
      listGetD fiber75OuterChunks 10 [] := by
  decide

theorem fiber75_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks 11 []) =
      listGetD fiber75OuterChunks 11 [] := by
  decide

theorem fiber75_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast75
        (listGetD tauStateChunks idx []) =
      listGetD fiber75OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber75_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber75_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber75_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber75_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber75_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber75_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber75_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber75_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber75_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber75_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber75_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber75_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber75_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast75 =
      fiber75 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast75 tauStateChunks fiber75OuterChunks
    tauStateChunks_eq (by rfl) fiber75_outer_get
  simpa [fiber75] using h

theorem fiber75_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.b, LColor.r] = fiber75 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.b, LColor.r] keyedLast75_eq
  exact hfrom.trans fiber75_keyedFrom_eq

theorem fiber75_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.b, LColor.r] = fiber75 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.mirror [LColor.p, LColor.p, LColor.b, LColor.r]
  exact hfast.trans fiber75_keyed_eq

theorem cert75_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.b, LColor.r] = [] := by
  have hnil : fiber75 = [] := by
    decide
  exact fiber75_eq.trans hnil

theorem cert75_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert75_empty


end GoertzelLemma818ClosedCollarS2Word11
end Mettapedia.GraphTheory.FourColor
