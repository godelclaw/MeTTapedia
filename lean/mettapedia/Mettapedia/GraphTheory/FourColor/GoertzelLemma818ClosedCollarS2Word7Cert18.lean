import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast18 : List TauState :=
  [stateAt 6, stateAt 14, stateAt 22, stateAt 30]

theorem keyedLast18_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.r, LColor.r]) =
      keyedLast18 := by
  decide

def fiber18OuterChunks : List (List (List TauState)) :=
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

def fiber18 : List (List TauState) :=
  fiber18OuterChunks.flatten

theorem fiber18_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 0 []) =
      listGetD fiber18OuterChunks 0 [] := by
  decide

theorem fiber18_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 1 []) =
      listGetD fiber18OuterChunks 1 [] := by
  decide

theorem fiber18_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 2 []) =
      listGetD fiber18OuterChunks 2 [] := by
  decide

theorem fiber18_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 3 []) =
      listGetD fiber18OuterChunks 3 [] := by
  decide

theorem fiber18_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 4 []) =
      listGetD fiber18OuterChunks 4 [] := by
  decide

theorem fiber18_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 5 []) =
      listGetD fiber18OuterChunks 5 [] := by
  decide

theorem fiber18_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 6 []) =
      listGetD fiber18OuterChunks 6 [] := by
  decide

theorem fiber18_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 7 []) =
      listGetD fiber18OuterChunks 7 [] := by
  decide

theorem fiber18_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 8 []) =
      listGetD fiber18OuterChunks 8 [] := by
  decide

theorem fiber18_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 9 []) =
      listGetD fiber18OuterChunks 9 [] := by
  decide

theorem fiber18_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 10 []) =
      listGetD fiber18OuterChunks 10 [] := by
  decide

theorem fiber18_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks 11 []) =
      listGetD fiber18OuterChunks 11 [] := by
  decide

theorem fiber18_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast18
        (listGetD tauStateChunks idx []) =
      listGetD fiber18OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber18_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber18_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber18_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber18_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber18_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber18_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber18_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber18_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber18_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber18_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber18_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber18_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber18_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast18 =
      fiber18 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast18 tauStateChunks fiber18OuterChunks
    tauStateChunks_eq (by rfl) fiber18_outer_get
  simpa [fiber18] using h

theorem fiber18_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.r, LColor.r] = fiber18 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.r, LColor.r] keyedLast18_eq
  exact hfrom.trans fiber18_keyedFrom_eq

theorem fiber18_eq :
    closedCollarFiber word [LColor.r, LColor.p, LColor.r, LColor.r] = fiber18 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.r, LColor.p, LColor.r, LColor.r]
  exact hfast.trans fiber18_keyed_eq

theorem cert18_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.r, LColor.r] = [] := by
  have hnil : fiber18 = [] := by
    decide
  exact fiber18_eq.trans hnil

theorem cert18_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert18_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
