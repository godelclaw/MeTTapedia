import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word10Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word10

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast17 : List TauState :=
  [stateAt 36, stateAt 44, stateAt 52, stateAt 60]

theorem keyedLast17_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.p, LColor.p]) =
      keyedLast17 := by
  decide

def fiber17OuterChunks : List (List (List TauState)) :=
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

def fiber17 : List (List TauState) :=
  fiber17OuterChunks.flatten

theorem fiber17_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 0 []) =
      listGetD fiber17OuterChunks 0 [] := by
  decide

theorem fiber17_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 1 []) =
      listGetD fiber17OuterChunks 1 [] := by
  decide

theorem fiber17_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 2 []) =
      listGetD fiber17OuterChunks 2 [] := by
  decide

theorem fiber17_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 3 []) =
      listGetD fiber17OuterChunks 3 [] := by
  decide

theorem fiber17_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 4 []) =
      listGetD fiber17OuterChunks 4 [] := by
  decide

theorem fiber17_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 5 []) =
      listGetD fiber17OuterChunks 5 [] := by
  decide

theorem fiber17_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 6 []) =
      listGetD fiber17OuterChunks 6 [] := by
  decide

theorem fiber17_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 7 []) =
      listGetD fiber17OuterChunks 7 [] := by
  decide

theorem fiber17_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 8 []) =
      listGetD fiber17OuterChunks 8 [] := by
  decide

theorem fiber17_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 9 []) =
      listGetD fiber17OuterChunks 9 [] := by
  decide

theorem fiber17_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 10 []) =
      listGetD fiber17OuterChunks 10 [] := by
  decide

theorem fiber17_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks 11 []) =
      listGetD fiber17OuterChunks 11 [] := by
  decide

theorem fiber17_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast17
        (listGetD tauStateChunks idx []) =
      listGetD fiber17OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber17_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber17_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber17_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber17_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber17_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber17_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber17_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber17_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber17_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber17_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber17_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber17_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber17_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast17 =
      fiber17 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast17 tauStateChunks fiber17OuterChunks
    tauStateChunks_eq (by rfl) fiber17_outer_get
  simpa [fiber17] using h

theorem fiber17_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.p, LColor.p] = fiber17 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.p, LColor.p] keyedLast17_eq
  exact hfrom.trans fiber17_keyedFrom_eq

theorem fiber17_eq :
    closedCollarFiber word [LColor.r, LColor.b, LColor.p, LColor.p] = fiber17 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.normal [LColor.r, LColor.b, LColor.p, LColor.p]
  exact hfast.trans fiber17_keyed_eq

theorem cert17_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.p, LColor.p] = [] := by
  have hnil : fiber17 = [] := by
    decide
  exact fiber17_eq.trans hnil

theorem cert17_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert17_empty


end GoertzelLemma818ClosedCollarS2Word10
end Mettapedia.GraphTheory.FourColor
