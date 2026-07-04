import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast42 : List TauState :=
  [stateAt 5, stateAt 13, stateAt 21, stateAt 29]

theorem keyedLast42_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.p, LColor.r]) =
      keyedLast42 := by
  decide

def fiber42OuterChunks : List (List (List TauState)) :=
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

def fiber42 : List (List TauState) :=
  fiber42OuterChunks.flatten

theorem fiber42_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 0 []) =
      listGetD fiber42OuterChunks 0 [] := by
  decide

theorem fiber42_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 1 []) =
      listGetD fiber42OuterChunks 1 [] := by
  decide

theorem fiber42_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 2 []) =
      listGetD fiber42OuterChunks 2 [] := by
  decide

theorem fiber42_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 3 []) =
      listGetD fiber42OuterChunks 3 [] := by
  decide

theorem fiber42_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 4 []) =
      listGetD fiber42OuterChunks 4 [] := by
  decide

theorem fiber42_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 5 []) =
      listGetD fiber42OuterChunks 5 [] := by
  decide

theorem fiber42_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 6 []) =
      listGetD fiber42OuterChunks 6 [] := by
  decide

theorem fiber42_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 7 []) =
      listGetD fiber42OuterChunks 7 [] := by
  decide

theorem fiber42_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 8 []) =
      listGetD fiber42OuterChunks 8 [] := by
  decide

theorem fiber42_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 9 []) =
      listGetD fiber42OuterChunks 9 [] := by
  decide

theorem fiber42_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 10 []) =
      listGetD fiber42OuterChunks 10 [] := by
  decide

theorem fiber42_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks 11 []) =
      listGetD fiber42OuterChunks 11 [] := by
  decide

theorem fiber42_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast42
        (listGetD tauStateChunks idx []) =
      listGetD fiber42OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber42_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber42_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber42_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber42_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber42_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber42_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber42_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber42_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber42_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber42_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber42_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber42_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber42_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast42 =
      fiber42 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast42 tauStateChunks fiber42OuterChunks
    tauStateChunks_eq (by rfl) fiber42_outer_get
  simpa [fiber42] using h

theorem fiber42_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.p, LColor.r] = fiber42 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.p, LColor.r] keyedLast42_eq
  exact hfrom.trans fiber42_keyedFrom_eq

theorem fiber42_eq :
    closedCollarFiber word [LColor.b, LColor.b, LColor.p, LColor.r] = fiber42 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.b, LColor.p, LColor.r]
  exact hfast.trans fiber42_keyed_eq

theorem cert42_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.p, LColor.r] = [] := by
  have hnil : fiber42 = [] := by
    decide
  exact fiber42_eq.trans hnil

theorem cert42_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert42_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
