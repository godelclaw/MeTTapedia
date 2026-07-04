import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word11

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast61 : List TauState :=
  [stateAt 97, stateAt 105, stateAt 113, stateAt 121]

theorem keyedLast61_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.p, LColor.b]) =
      keyedLast61 := by
  decide

def fiber61OuterChunks : List (List (List TauState)) :=
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

def fiber61 : List (List TauState) :=
  fiber61OuterChunks.flatten

theorem fiber61_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 0 []) =
      listGetD fiber61OuterChunks 0 [] := by
  decide

theorem fiber61_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 1 []) =
      listGetD fiber61OuterChunks 1 [] := by
  decide

theorem fiber61_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 2 []) =
      listGetD fiber61OuterChunks 2 [] := by
  decide

theorem fiber61_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 3 []) =
      listGetD fiber61OuterChunks 3 [] := by
  decide

theorem fiber61_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 4 []) =
      listGetD fiber61OuterChunks 4 [] := by
  decide

theorem fiber61_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 5 []) =
      listGetD fiber61OuterChunks 5 [] := by
  decide

theorem fiber61_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 6 []) =
      listGetD fiber61OuterChunks 6 [] := by
  decide

theorem fiber61_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 7 []) =
      listGetD fiber61OuterChunks 7 [] := by
  decide

theorem fiber61_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 8 []) =
      listGetD fiber61OuterChunks 8 [] := by
  decide

theorem fiber61_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 9 []) =
      listGetD fiber61OuterChunks 9 [] := by
  decide

theorem fiber61_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 10 []) =
      listGetD fiber61OuterChunks 10 [] := by
  decide

theorem fiber61_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks 11 []) =
      listGetD fiber61OuterChunks 11 [] := by
  decide

theorem fiber61_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast61
        (listGetD tauStateChunks idx []) =
      listGetD fiber61OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber61_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber61_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber61_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber61_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber61_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber61_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber61_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber61_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber61_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber61_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber61_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber61_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber61_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast61 =
      fiber61 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast61 tauStateChunks fiber61OuterChunks
    tauStateChunks_eq (by rfl) fiber61_outer_get
  simpa [fiber61] using h

theorem fiber61_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.p, LColor.b] = fiber61 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.p, LColor.b] keyedLast61_eq
  exact hfrom.trans fiber61_keyedFrom_eq

theorem fiber61_eq :
    closedCollarFiber word [LColor.p, LColor.r, LColor.p, LColor.b] = fiber61 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.mirror [LColor.p, LColor.r, LColor.p, LColor.b]
  exact hfast.trans fiber61_keyed_eq

theorem cert61_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.p, LColor.b] = [] := by
  have hnil : fiber61 = [] := by
    decide
  exact fiber61_eq.trans hnil

theorem cert61_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert61_empty


end GoertzelLemma818ClosedCollarS2Word11
end Mettapedia.GraphTheory.FourColor
