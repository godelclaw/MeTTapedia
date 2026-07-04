import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast19 : List TauState :=
  [stateAt 70, stateAt 78, stateAt 86, stateAt 94]

theorem keyedLast19_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.r, LColor.b]) =
      keyedLast19 := by
  decide

def fiber19OuterChunks : List (List (List TauState)) :=
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

def fiber19 : List (List TauState) :=
  fiber19OuterChunks.flatten

theorem fiber19_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 0 []) =
      listGetD fiber19OuterChunks 0 [] := by
  decide

theorem fiber19_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 1 []) =
      listGetD fiber19OuterChunks 1 [] := by
  decide

theorem fiber19_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 2 []) =
      listGetD fiber19OuterChunks 2 [] := by
  decide

theorem fiber19_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 3 []) =
      listGetD fiber19OuterChunks 3 [] := by
  decide

theorem fiber19_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 4 []) =
      listGetD fiber19OuterChunks 4 [] := by
  decide

theorem fiber19_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 5 []) =
      listGetD fiber19OuterChunks 5 [] := by
  decide

theorem fiber19_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 6 []) =
      listGetD fiber19OuterChunks 6 [] := by
  decide

theorem fiber19_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 7 []) =
      listGetD fiber19OuterChunks 7 [] := by
  decide

theorem fiber19_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 8 []) =
      listGetD fiber19OuterChunks 8 [] := by
  decide

theorem fiber19_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 9 []) =
      listGetD fiber19OuterChunks 9 [] := by
  decide

theorem fiber19_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 10 []) =
      listGetD fiber19OuterChunks 10 [] := by
  decide

theorem fiber19_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks 11 []) =
      listGetD fiber19OuterChunks 11 [] := by
  decide

theorem fiber19_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast19
        (listGetD tauStateChunks idx []) =
      listGetD fiber19OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber19_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber19_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber19_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber19_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber19_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber19_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber19_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber19_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber19_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber19_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber19_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber19_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber19_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast19 =
      fiber19 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast19 tauStateChunks fiber19OuterChunks
    tauStateChunks_eq (by rfl) fiber19_outer_get
  simpa [fiber19] using h

theorem fiber19_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.r, LColor.b] = fiber19 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.r, LColor.b] keyedLast19_eq
  exact hfrom.trans fiber19_keyedFrom_eq

theorem fiber19_eq :
    closedCollarFiber word [LColor.r, LColor.p, LColor.r, LColor.b] = fiber19 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.r, LColor.b]
  exact hfast.trans fiber19_keyed_eq

theorem cert19_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.r, LColor.b] = [] := by
  have hnil : fiber19 = [] := by
    decide
  exact fiber19_eq.trans hnil

theorem cert19_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert19_empty


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
