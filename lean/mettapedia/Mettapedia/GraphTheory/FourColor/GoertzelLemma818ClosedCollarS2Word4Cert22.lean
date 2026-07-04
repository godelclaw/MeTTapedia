import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word4

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast22 : List TauState :=
  [stateAt 5, stateAt 13, stateAt 21, stateAt 29]

theorem keyedLast22_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.b, LColor.b]) =
      keyedLast22 := by
  decide

def fiber22OuterChunks : List (List (List TauState)) :=
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

def fiber22 : List (List TauState) :=
  fiber22OuterChunks.flatten

theorem fiber22_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 0 []) =
      listGetD fiber22OuterChunks 0 [] := by
  decide

theorem fiber22_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 1 []) =
      listGetD fiber22OuterChunks 1 [] := by
  decide

theorem fiber22_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 2 []) =
      listGetD fiber22OuterChunks 2 [] := by
  decide

theorem fiber22_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 3 []) =
      listGetD fiber22OuterChunks 3 [] := by
  decide

theorem fiber22_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 4 []) =
      listGetD fiber22OuterChunks 4 [] := by
  decide

theorem fiber22_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 5 []) =
      listGetD fiber22OuterChunks 5 [] := by
  decide

theorem fiber22_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 6 []) =
      listGetD fiber22OuterChunks 6 [] := by
  decide

theorem fiber22_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 7 []) =
      listGetD fiber22OuterChunks 7 [] := by
  decide

theorem fiber22_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 8 []) =
      listGetD fiber22OuterChunks 8 [] := by
  decide

theorem fiber22_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 9 []) =
      listGetD fiber22OuterChunks 9 [] := by
  decide

theorem fiber22_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 10 []) =
      listGetD fiber22OuterChunks 10 [] := by
  decide

theorem fiber22_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks 11 []) =
      listGetD fiber22OuterChunks 11 [] := by
  decide

theorem fiber22_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast22
        (listGetD tauStateChunks idx []) =
      listGetD fiber22OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber22_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber22_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber22_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber22_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber22_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber22_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber22_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber22_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber22_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber22_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber22_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber22_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber22_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast22 =
      fiber22 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast22 tauStateChunks fiber22OuterChunks
    tauStateChunks_eq (by rfl) fiber22_outer_get
  simpa [fiber22] using h

theorem fiber22_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.b, LColor.b] = fiber22 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.b, LColor.b] keyedLast22_eq
  exact hfrom.trans fiber22_keyedFrom_eq

theorem fiber22_eq :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.b] = fiber22 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.normal [LColor.r, LColor.p, LColor.b, LColor.b]
  exact hfast.trans fiber22_keyed_eq

theorem cert22_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.b] = [] := by
  have hnil : fiber22 = [] := by
    decide
  exact fiber22_eq.trans hnil

theorem cert22_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert22_empty


end GoertzelLemma818ClosedCollarS2Word4
end Mettapedia.GraphTheory.FourColor
