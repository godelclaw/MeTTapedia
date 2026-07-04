import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast74 : List TauState :=
  [stateAt 160, stateAt 168, stateAt 176, stateAt 184]

theorem keyedLast74_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.r, LColor.p]) =
      keyedLast74 := by
  decide

def fiber74OuterChunks : List (List (List TauState)) :=
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

def fiber74 : List (List TauState) :=
  fiber74OuterChunks.flatten

theorem fiber74_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 0 []) =
      listGetD fiber74OuterChunks 0 [] := by
  decide

theorem fiber74_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 1 []) =
      listGetD fiber74OuterChunks 1 [] := by
  decide

theorem fiber74_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 2 []) =
      listGetD fiber74OuterChunks 2 [] := by
  decide

theorem fiber74_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 3 []) =
      listGetD fiber74OuterChunks 3 [] := by
  decide

theorem fiber74_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 4 []) =
      listGetD fiber74OuterChunks 4 [] := by
  decide

theorem fiber74_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 5 []) =
      listGetD fiber74OuterChunks 5 [] := by
  decide

theorem fiber74_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 6 []) =
      listGetD fiber74OuterChunks 6 [] := by
  decide

theorem fiber74_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 7 []) =
      listGetD fiber74OuterChunks 7 [] := by
  decide

theorem fiber74_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 8 []) =
      listGetD fiber74OuterChunks 8 [] := by
  decide

theorem fiber74_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 9 []) =
      listGetD fiber74OuterChunks 9 [] := by
  decide

theorem fiber74_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 10 []) =
      listGetD fiber74OuterChunks 10 [] := by
  decide

theorem fiber74_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks 11 []) =
      listGetD fiber74OuterChunks 11 [] := by
  decide

theorem fiber74_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast74
        (listGetD tauStateChunks idx []) =
      listGetD fiber74OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber74_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber74_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber74_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber74_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber74_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber74_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber74_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber74_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber74_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber74_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber74_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber74_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber74_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast74 =
      fiber74 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast74 tauStateChunks fiber74OuterChunks
    tauStateChunks_eq (by rfl) fiber74_outer_get
  simpa [fiber74] using h

theorem fiber74_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.r, LColor.p] = fiber74 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.r, LColor.p] keyedLast74_eq
  exact hfrom.trans fiber74_keyedFrom_eq

theorem fiber74_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.r, LColor.p] = fiber74 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.r, LColor.p]
  exact hfast.trans fiber74_keyed_eq

theorem cert74_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.r, LColor.p] = [] := by
  have hnil : fiber74 = [] := by
    decide
  exact fiber74_eq.trans hnil

theorem cert74_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert74_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
