import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word4

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast33 : List TauState :=
  [stateAt 70, stateAt 78, stateAt 86, stateAt 94]

theorem keyedLast33_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.p, LColor.r]) =
      keyedLast33 := by
  decide

def fiber33OuterChunks : List (List (List TauState)) :=
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

def fiber33 : List (List TauState) :=
  fiber33OuterChunks.flatten

theorem fiber33_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 0 []) =
      listGetD fiber33OuterChunks 0 [] := by
  decide

theorem fiber33_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 1 []) =
      listGetD fiber33OuterChunks 1 [] := by
  decide

theorem fiber33_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 2 []) =
      listGetD fiber33OuterChunks 2 [] := by
  decide

theorem fiber33_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 3 []) =
      listGetD fiber33OuterChunks 3 [] := by
  decide

theorem fiber33_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 4 []) =
      listGetD fiber33OuterChunks 4 [] := by
  decide

theorem fiber33_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 5 []) =
      listGetD fiber33OuterChunks 5 [] := by
  decide

theorem fiber33_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 6 []) =
      listGetD fiber33OuterChunks 6 [] := by
  decide

theorem fiber33_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 7 []) =
      listGetD fiber33OuterChunks 7 [] := by
  decide

theorem fiber33_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 8 []) =
      listGetD fiber33OuterChunks 8 [] := by
  decide

theorem fiber33_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 9 []) =
      listGetD fiber33OuterChunks 9 [] := by
  decide

theorem fiber33_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 10 []) =
      listGetD fiber33OuterChunks 10 [] := by
  decide

theorem fiber33_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks 11 []) =
      listGetD fiber33OuterChunks 11 [] := by
  decide

theorem fiber33_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast33
        (listGetD tauStateChunks idx []) =
      listGetD fiber33OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber33_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber33_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber33_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber33_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber33_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber33_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber33_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber33_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber33_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber33_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber33_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber33_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber33_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast33 =
      fiber33 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast33 tauStateChunks fiber33OuterChunks
    tauStateChunks_eq (by rfl) fiber33_outer_get
  simpa [fiber33] using h

theorem fiber33_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.p, LColor.r] = fiber33 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.p, LColor.r] keyedLast33_eq
  exact hfrom.trans fiber33_keyedFrom_eq

theorem fiber33_eq :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.r] = fiber33 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.normal [LColor.b, LColor.r, LColor.p, LColor.r]
  exact hfast.trans fiber33_keyed_eq

theorem cert33_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.r] = [] := by
  have hnil : fiber33 = [] := by
    decide
  exact fiber33_eq.trans hnil

theorem cert33_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert33_empty


end GoertzelLemma818ClosedCollarS2Word4
end Mettapedia.GraphTheory.FourColor
