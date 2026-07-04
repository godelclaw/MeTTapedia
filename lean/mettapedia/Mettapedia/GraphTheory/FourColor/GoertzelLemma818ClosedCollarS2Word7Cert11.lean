import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast11 : List TauState :=
  [stateAt 130, stateAt 138, stateAt 146, stateAt 154]

theorem keyedLast11_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.r, LColor.p]) =
      keyedLast11 := by
  decide

def fiber11OuterChunks : List (List (List TauState)) :=
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

def fiber11 : List (List TauState) :=
  fiber11OuterChunks.flatten

theorem fiber11_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 0 []) =
      listGetD fiber11OuterChunks 0 [] := by
  decide

theorem fiber11_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 1 []) =
      listGetD fiber11OuterChunks 1 [] := by
  decide

theorem fiber11_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 2 []) =
      listGetD fiber11OuterChunks 2 [] := by
  decide

theorem fiber11_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 3 []) =
      listGetD fiber11OuterChunks 3 [] := by
  decide

theorem fiber11_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 4 []) =
      listGetD fiber11OuterChunks 4 [] := by
  decide

theorem fiber11_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 5 []) =
      listGetD fiber11OuterChunks 5 [] := by
  decide

theorem fiber11_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 6 []) =
      listGetD fiber11OuterChunks 6 [] := by
  decide

theorem fiber11_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 7 []) =
      listGetD fiber11OuterChunks 7 [] := by
  decide

theorem fiber11_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 8 []) =
      listGetD fiber11OuterChunks 8 [] := by
  decide

theorem fiber11_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 9 []) =
      listGetD fiber11OuterChunks 9 [] := by
  decide

theorem fiber11_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 10 []) =
      listGetD fiber11OuterChunks 10 [] := by
  decide

theorem fiber11_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks 11 []) =
      listGetD fiber11OuterChunks 11 [] := by
  decide

theorem fiber11_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast11
        (listGetD tauStateChunks idx []) =
      listGetD fiber11OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber11_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber11_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber11_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber11_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber11_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber11_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber11_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber11_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber11_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber11_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber11_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber11_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber11_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast11 =
      fiber11 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast11 tauStateChunks fiber11OuterChunks
    tauStateChunks_eq (by rfl) fiber11_outer_get
  simpa [fiber11] using h

theorem fiber11_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.r, LColor.p] = fiber11 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.r, LColor.p] keyedLast11_eq
  exact hfrom.trans fiber11_keyedFrom_eq

theorem fiber11_eq :
    closedCollarFiber word [LColor.r, LColor.b, LColor.r, LColor.p] = fiber11 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.r, LColor.b, LColor.r, LColor.p]
  exact hfast.trans fiber11_keyed_eq

theorem cert11_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.r, LColor.p] = [] := by
  have hnil : fiber11 = [] := by
    decide
  exact fiber11_eq.trans hnil

theorem cert11_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert11_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
