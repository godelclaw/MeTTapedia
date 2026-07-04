import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word4

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast9 : List TauState :=
  [stateAt 39, stateAt 47, stateAt 55, stateAt 63]

theorem keyedLast9_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.r, LColor.r]) =
      keyedLast9 := by
  decide

def fiber9OuterChunks : List (List (List TauState)) :=
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

def fiber9 : List (List TauState) :=
  fiber9OuterChunks.flatten

theorem fiber9_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 0 []) =
      listGetD fiber9OuterChunks 0 [] := by
  decide

theorem fiber9_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 1 []) =
      listGetD fiber9OuterChunks 1 [] := by
  decide

theorem fiber9_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 2 []) =
      listGetD fiber9OuterChunks 2 [] := by
  decide

theorem fiber9_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 3 []) =
      listGetD fiber9OuterChunks 3 [] := by
  decide

theorem fiber9_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 4 []) =
      listGetD fiber9OuterChunks 4 [] := by
  decide

theorem fiber9_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 5 []) =
      listGetD fiber9OuterChunks 5 [] := by
  decide

theorem fiber9_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 6 []) =
      listGetD fiber9OuterChunks 6 [] := by
  decide

theorem fiber9_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 7 []) =
      listGetD fiber9OuterChunks 7 [] := by
  decide

theorem fiber9_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 8 []) =
      listGetD fiber9OuterChunks 8 [] := by
  decide

theorem fiber9_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 9 []) =
      listGetD fiber9OuterChunks 9 [] := by
  decide

theorem fiber9_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 10 []) =
      listGetD fiber9OuterChunks 10 [] := by
  decide

theorem fiber9_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks 11 []) =
      listGetD fiber9OuterChunks 11 [] := by
  decide

theorem fiber9_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast9
        (listGetD tauStateChunks idx []) =
      listGetD fiber9OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber9_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber9_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber9_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber9_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber9_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber9_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber9_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber9_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber9_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber9_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber9_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber9_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber9_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast9 =
      fiber9 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast9 tauStateChunks fiber9OuterChunks
    tauStateChunks_eq (by rfl) fiber9_outer_get
  simpa [fiber9] using h

theorem fiber9_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.r, LColor.r] = fiber9 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.r, LColor.r] keyedLast9_eq
  exact hfrom.trans fiber9_keyedFrom_eq

theorem fiber9_eq :
    closedCollarFiber word [LColor.r, LColor.b, LColor.r, LColor.r] = fiber9 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.normal [LColor.r, LColor.b, LColor.r, LColor.r]
  exact hfast.trans fiber9_keyed_eq

theorem cert9_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.r, LColor.r] = [] := by
  have hnil : fiber9 = [] := by
    decide
  exact fiber9_eq.trans hnil

theorem cert9_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert9_empty


end GoertzelLemma818ClosedCollarS2Word4
end Mettapedia.GraphTheory.FourColor
