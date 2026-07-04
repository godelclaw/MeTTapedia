import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast71 : List TauState :=
  [stateAt 129, stateAt 137, stateAt 145, stateAt 153]

theorem keyedLast71_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.p, LColor.p]) =
      keyedLast71 := by
  decide

def fiber71OuterChunks : List (List (List TauState)) :=
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

def fiber71 : List (List TauState) :=
  fiber71OuterChunks.flatten

theorem fiber71_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 0 []) =
      listGetD fiber71OuterChunks 0 [] := by
  decide

theorem fiber71_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 1 []) =
      listGetD fiber71OuterChunks 1 [] := by
  decide

theorem fiber71_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 2 []) =
      listGetD fiber71OuterChunks 2 [] := by
  decide

theorem fiber71_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 3 []) =
      listGetD fiber71OuterChunks 3 [] := by
  decide

theorem fiber71_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 4 []) =
      listGetD fiber71OuterChunks 4 [] := by
  decide

theorem fiber71_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 5 []) =
      listGetD fiber71OuterChunks 5 [] := by
  decide

theorem fiber71_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 6 []) =
      listGetD fiber71OuterChunks 6 [] := by
  decide

theorem fiber71_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 7 []) =
      listGetD fiber71OuterChunks 7 [] := by
  decide

theorem fiber71_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 8 []) =
      listGetD fiber71OuterChunks 8 [] := by
  decide

theorem fiber71_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 9 []) =
      listGetD fiber71OuterChunks 9 [] := by
  decide

theorem fiber71_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 10 []) =
      listGetD fiber71OuterChunks 10 [] := by
  decide

theorem fiber71_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks 11 []) =
      listGetD fiber71OuterChunks 11 [] := by
  decide

theorem fiber71_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast71
        (listGetD tauStateChunks idx []) =
      listGetD fiber71OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber71_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber71_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber71_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber71_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber71_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber71_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber71_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber71_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber71_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber71_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber71_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber71_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber71_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast71 =
      fiber71 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast71 tauStateChunks fiber71OuterChunks
    tauStateChunks_eq (by rfl) fiber71_outer_get
  simpa [fiber71] using h

theorem fiber71_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.p, LColor.p] = fiber71 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.p, LColor.p] keyedLast71_eq
  exact hfrom.trans fiber71_keyedFrom_eq

theorem fiber71_eq :
    closedCollarFiber word [LColor.p, LColor.b, LColor.p, LColor.p] = fiber71 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.p, LColor.b, LColor.p, LColor.p]
  exact hfast.trans fiber71_keyed_eq

theorem cert71_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.p, LColor.p] = [] := by
  have hnil : fiber71 = [] := by
    decide
  exact fiber71_eq.trans hnil

theorem cert71_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert71_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
