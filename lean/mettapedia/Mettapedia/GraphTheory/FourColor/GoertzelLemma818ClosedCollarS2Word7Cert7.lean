import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast7 : List TauState :=
  [stateAt 71, stateAt 79, stateAt 87, stateAt 95]

theorem keyedLast7_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.p, LColor.b]) =
      keyedLast7 := by
  decide

def fiber7OuterChunks : List (List (List TauState)) :=
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

def fiber7 : List (List TauState) :=
  fiber7OuterChunks.flatten

theorem fiber7_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 0 []) =
      listGetD fiber7OuterChunks 0 [] := by
  decide

theorem fiber7_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 1 []) =
      listGetD fiber7OuterChunks 1 [] := by
  decide

theorem fiber7_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 2 []) =
      listGetD fiber7OuterChunks 2 [] := by
  decide

theorem fiber7_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 3 []) =
      listGetD fiber7OuterChunks 3 [] := by
  decide

theorem fiber7_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 4 []) =
      listGetD fiber7OuterChunks 4 [] := by
  decide

theorem fiber7_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 5 []) =
      listGetD fiber7OuterChunks 5 [] := by
  decide

theorem fiber7_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 6 []) =
      listGetD fiber7OuterChunks 6 [] := by
  decide

theorem fiber7_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 7 []) =
      listGetD fiber7OuterChunks 7 [] := by
  decide

theorem fiber7_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 8 []) =
      listGetD fiber7OuterChunks 8 [] := by
  decide

theorem fiber7_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 9 []) =
      listGetD fiber7OuterChunks 9 [] := by
  decide

theorem fiber7_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 10 []) =
      listGetD fiber7OuterChunks 10 [] := by
  decide

theorem fiber7_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks 11 []) =
      listGetD fiber7OuterChunks 11 [] := by
  decide

theorem fiber7_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast7
        (listGetD tauStateChunks idx []) =
      listGetD fiber7OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber7_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber7_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber7_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber7_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber7_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber7_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber7_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber7_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber7_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber7_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber7_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber7_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber7_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast7 =
      fiber7 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast7 tauStateChunks fiber7OuterChunks
    tauStateChunks_eq (by rfl) fiber7_outer_get
  simpa [fiber7] using h

theorem fiber7_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.p, LColor.b] = fiber7 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.p, LColor.b] keyedLast7_eq
  exact hfrom.trans fiber7_keyedFrom_eq

theorem fiber7_eq :
    closedCollarFiber word [LColor.r, LColor.r, LColor.p, LColor.b] = fiber7 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.r, LColor.r, LColor.p, LColor.b]
  exact hfast.trans fiber7_keyed_eq

theorem cert7_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.p, LColor.b] = [] := by
  have hnil : fiber7 = [] := by
    decide
  exact fiber7_eq.trans hnil

theorem cert7_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert7_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
