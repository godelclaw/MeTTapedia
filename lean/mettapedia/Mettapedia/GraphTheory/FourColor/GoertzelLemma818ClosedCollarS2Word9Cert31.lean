import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast31 : List TauState :=
  [stateAt 99, stateAt 107, stateAt 115, stateAt 123]

theorem keyedLast31_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.b, LColor.b]) =
      keyedLast31 := by
  decide

def fiber31OuterChunks : List (List (List TauState)) :=
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

def fiber31 : List (List TauState) :=
  fiber31OuterChunks.flatten

theorem fiber31_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 0 []) =
      listGetD fiber31OuterChunks 0 [] := by
  decide

theorem fiber31_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 1 []) =
      listGetD fiber31OuterChunks 1 [] := by
  decide

theorem fiber31_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 2 []) =
      listGetD fiber31OuterChunks 2 [] := by
  decide

theorem fiber31_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 3 []) =
      listGetD fiber31OuterChunks 3 [] := by
  decide

theorem fiber31_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 4 []) =
      listGetD fiber31OuterChunks 4 [] := by
  decide

theorem fiber31_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 5 []) =
      listGetD fiber31OuterChunks 5 [] := by
  decide

theorem fiber31_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 6 []) =
      listGetD fiber31OuterChunks 6 [] := by
  decide

theorem fiber31_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 7 []) =
      listGetD fiber31OuterChunks 7 [] := by
  decide

theorem fiber31_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 8 []) =
      listGetD fiber31OuterChunks 8 [] := by
  decide

theorem fiber31_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 9 []) =
      listGetD fiber31OuterChunks 9 [] := by
  decide

theorem fiber31_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 10 []) =
      listGetD fiber31OuterChunks 10 [] := by
  decide

theorem fiber31_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks 11 []) =
      listGetD fiber31OuterChunks 11 [] := by
  decide

theorem fiber31_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast31
        (listGetD tauStateChunks idx []) =
      listGetD fiber31OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber31_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber31_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber31_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber31_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber31_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber31_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber31_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber31_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber31_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber31_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber31_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber31_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber31_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast31 =
      fiber31 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast31 tauStateChunks fiber31OuterChunks
    tauStateChunks_eq (by rfl) fiber31_outer_get
  simpa [fiber31] using h

theorem fiber31_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.b, LColor.b] = fiber31 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.b, LColor.b] keyedLast31_eq
  exact hfrom.trans fiber31_keyedFrom_eq

theorem fiber31_eq :
    closedCollarFiber word [LColor.b, LColor.r, LColor.b, LColor.b] = fiber31 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.b, LColor.b]
  exact hfast.trans fiber31_keyed_eq

theorem cert31_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.b, LColor.b] = [] := by
  have hnil : fiber31 = [] := by
    decide
  exact fiber31_eq.trans hnil

theorem cert31_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert31_empty


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
