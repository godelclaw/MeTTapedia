import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word4

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast57 : List TauState :=
  [stateAt 130, stateAt 138, stateAt 146, stateAt 154]

theorem keyedLast57_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.b, LColor.r]) =
      keyedLast57 := by
  decide

def fiber57OuterChunks : List (List (List TauState)) :=
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

def fiber57 : List (List TauState) :=
  fiber57OuterChunks.flatten

theorem fiber57_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 0 []) =
      listGetD fiber57OuterChunks 0 [] := by
  decide

theorem fiber57_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 1 []) =
      listGetD fiber57OuterChunks 1 [] := by
  decide

theorem fiber57_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 2 []) =
      listGetD fiber57OuterChunks 2 [] := by
  decide

theorem fiber57_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 3 []) =
      listGetD fiber57OuterChunks 3 [] := by
  decide

theorem fiber57_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 4 []) =
      listGetD fiber57OuterChunks 4 [] := by
  decide

theorem fiber57_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 5 []) =
      listGetD fiber57OuterChunks 5 [] := by
  decide

theorem fiber57_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 6 []) =
      listGetD fiber57OuterChunks 6 [] := by
  decide

theorem fiber57_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 7 []) =
      listGetD fiber57OuterChunks 7 [] := by
  decide

theorem fiber57_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 8 []) =
      listGetD fiber57OuterChunks 8 [] := by
  decide

theorem fiber57_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 9 []) =
      listGetD fiber57OuterChunks 9 [] := by
  decide

theorem fiber57_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 10 []) =
      listGetD fiber57OuterChunks 10 [] := by
  decide

theorem fiber57_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks 11 []) =
      listGetD fiber57OuterChunks 11 [] := by
  decide

theorem fiber57_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast57
        (listGetD tauStateChunks idx []) =
      listGetD fiber57OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber57_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber57_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber57_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber57_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber57_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber57_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber57_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber57_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber57_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber57_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber57_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber57_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber57_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast57 =
      fiber57 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast57 tauStateChunks fiber57OuterChunks
    tauStateChunks_eq (by rfl) fiber57_outer_get
  simpa [fiber57] using h

theorem fiber57_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.b, LColor.r] = fiber57 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.b, LColor.r] keyedLast57_eq
  exact hfrom.trans fiber57_keyedFrom_eq

theorem fiber57_eq :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.r] = fiber57 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.normal [LColor.p, LColor.r, LColor.b, LColor.r]
  exact hfast.trans fiber57_keyed_eq

theorem cert57_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.r] = [] := by
  have hnil : fiber57 = [] := by
    decide
  exact fiber57_eq.trans hnil

theorem cert57_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert57_empty


end GoertzelLemma818ClosedCollarS2Word4
end Mettapedia.GraphTheory.FourColor
