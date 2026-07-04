import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word10Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word10

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast45 : List TauState :=
  [stateAt 71, stateAt 79, stateAt 87, stateAt 95]

theorem keyedLast45_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.r, LColor.r]) =
      keyedLast45 := by
  decide

def fiber45OuterChunks : List (List (List TauState)) :=
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

def fiber45 : List (List TauState) :=
  fiber45OuterChunks.flatten

theorem fiber45_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 0 []) =
      listGetD fiber45OuterChunks 0 [] := by
  decide

theorem fiber45_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 1 []) =
      listGetD fiber45OuterChunks 1 [] := by
  decide

theorem fiber45_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 2 []) =
      listGetD fiber45OuterChunks 2 [] := by
  decide

theorem fiber45_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 3 []) =
      listGetD fiber45OuterChunks 3 [] := by
  decide

theorem fiber45_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 4 []) =
      listGetD fiber45OuterChunks 4 [] := by
  decide

theorem fiber45_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 5 []) =
      listGetD fiber45OuterChunks 5 [] := by
  decide

theorem fiber45_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 6 []) =
      listGetD fiber45OuterChunks 6 [] := by
  decide

theorem fiber45_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 7 []) =
      listGetD fiber45OuterChunks 7 [] := by
  decide

theorem fiber45_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 8 []) =
      listGetD fiber45OuterChunks 8 [] := by
  decide

theorem fiber45_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 9 []) =
      listGetD fiber45OuterChunks 9 [] := by
  decide

theorem fiber45_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 10 []) =
      listGetD fiber45OuterChunks 10 [] := by
  decide

theorem fiber45_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks 11 []) =
      listGetD fiber45OuterChunks 11 [] := by
  decide

theorem fiber45_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast45
        (listGetD tauStateChunks idx []) =
      listGetD fiber45OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber45_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber45_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber45_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber45_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber45_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber45_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber45_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber45_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber45_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber45_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber45_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber45_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber45_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast45 =
      fiber45 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast45 tauStateChunks fiber45OuterChunks
    tauStateChunks_eq (by rfl) fiber45_outer_get
  simpa [fiber45] using h

theorem fiber45_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.r, LColor.r] = fiber45 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.r, LColor.r] keyedLast45_eq
  exact hfrom.trans fiber45_keyedFrom_eq

theorem fiber45_eq :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.r] = fiber45 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.normal [LColor.b, LColor.p, LColor.r, LColor.r]
  exact hfast.trans fiber45_keyed_eq

theorem cert45_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.r] = [] := by
  have hnil : fiber45 = [] := by
    decide
  exact fiber45_eq.trans hnil

theorem cert45_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert45_empty


end GoertzelLemma818ClosedCollarS2Word10
end Mettapedia.GraphTheory.FourColor
