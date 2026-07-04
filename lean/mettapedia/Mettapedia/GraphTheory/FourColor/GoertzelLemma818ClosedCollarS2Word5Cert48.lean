import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast48 : List TauState :=
  [stateAt 4, stateAt 12, stateAt 20, stateAt 28]

theorem keyedLast48_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.b, LColor.r]) =
      keyedLast48 := by
  decide

def fiber48OuterChunks : List (List (List TauState)) :=
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

def fiber48 : List (List TauState) :=
  fiber48OuterChunks.flatten

theorem fiber48_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 0 []) =
      listGetD fiber48OuterChunks 0 [] := by
  decide

theorem fiber48_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 1 []) =
      listGetD fiber48OuterChunks 1 [] := by
  decide

theorem fiber48_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 2 []) =
      listGetD fiber48OuterChunks 2 [] := by
  decide

theorem fiber48_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 3 []) =
      listGetD fiber48OuterChunks 3 [] := by
  decide

theorem fiber48_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 4 []) =
      listGetD fiber48OuterChunks 4 [] := by
  decide

theorem fiber48_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 5 []) =
      listGetD fiber48OuterChunks 5 [] := by
  decide

theorem fiber48_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 6 []) =
      listGetD fiber48OuterChunks 6 [] := by
  decide

theorem fiber48_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 7 []) =
      listGetD fiber48OuterChunks 7 [] := by
  decide

theorem fiber48_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 8 []) =
      listGetD fiber48OuterChunks 8 [] := by
  decide

theorem fiber48_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 9 []) =
      listGetD fiber48OuterChunks 9 [] := by
  decide

theorem fiber48_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 10 []) =
      listGetD fiber48OuterChunks 10 [] := by
  decide

theorem fiber48_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks 11 []) =
      listGetD fiber48OuterChunks 11 [] := by
  decide

theorem fiber48_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast48
        (listGetD tauStateChunks idx []) =
      listGetD fiber48OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber48_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber48_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber48_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber48_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber48_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber48_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber48_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber48_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber48_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber48_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber48_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber48_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber48_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast48 =
      fiber48 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast48 tauStateChunks fiber48OuterChunks
    tauStateChunks_eq (by rfl) fiber48_outer_get
  simpa [fiber48] using h

theorem fiber48_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.b, LColor.r] = fiber48 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.b, LColor.r] keyedLast48_eq
  exact hfrom.trans fiber48_keyedFrom_eq

theorem fiber48_eq :
    closedCollarFiber word [LColor.b, LColor.p, LColor.b, LColor.r] = fiber48 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.b, LColor.r]
  exact hfast.trans fiber48_keyed_eq

theorem cert48_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.b, LColor.r] = [] := by
  have hnil : fiber48 = [] := by
    decide
  exact fiber48_eq.trans hnil

theorem cert48_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert48_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
