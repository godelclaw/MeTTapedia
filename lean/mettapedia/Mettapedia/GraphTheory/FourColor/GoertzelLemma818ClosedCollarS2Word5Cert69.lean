import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast69 : List TauState :=
  [stateAt 37, stateAt 45, stateAt 53, stateAt 61]

theorem keyedLast69_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.p, LColor.r]) =
      keyedLast69 := by
  decide

def fiber69OuterChunks : List (List (List TauState)) :=
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

def fiber69 : List (List TauState) :=
  fiber69OuterChunks.flatten

theorem fiber69_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 0 []) =
      listGetD fiber69OuterChunks 0 [] := by
  decide

theorem fiber69_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 1 []) =
      listGetD fiber69OuterChunks 1 [] := by
  decide

theorem fiber69_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 2 []) =
      listGetD fiber69OuterChunks 2 [] := by
  decide

theorem fiber69_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 3 []) =
      listGetD fiber69OuterChunks 3 [] := by
  decide

theorem fiber69_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 4 []) =
      listGetD fiber69OuterChunks 4 [] := by
  decide

theorem fiber69_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 5 []) =
      listGetD fiber69OuterChunks 5 [] := by
  decide

theorem fiber69_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 6 []) =
      listGetD fiber69OuterChunks 6 [] := by
  decide

theorem fiber69_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 7 []) =
      listGetD fiber69OuterChunks 7 [] := by
  decide

theorem fiber69_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 8 []) =
      listGetD fiber69OuterChunks 8 [] := by
  decide

theorem fiber69_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 9 []) =
      listGetD fiber69OuterChunks 9 [] := by
  decide

theorem fiber69_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 10 []) =
      listGetD fiber69OuterChunks 10 [] := by
  decide

theorem fiber69_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks 11 []) =
      listGetD fiber69OuterChunks 11 [] := by
  decide

theorem fiber69_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast69
        (listGetD tauStateChunks idx []) =
      listGetD fiber69OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber69_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber69_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber69_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber69_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber69_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber69_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber69_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber69_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber69_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber69_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber69_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber69_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber69_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast69 =
      fiber69 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast69 tauStateChunks fiber69OuterChunks
    tauStateChunks_eq (by rfl) fiber69_outer_get
  simpa [fiber69] using h

theorem fiber69_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.p, LColor.r] = fiber69 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.p, LColor.r] keyedLast69_eq
  exact hfrom.trans fiber69_keyedFrom_eq

theorem fiber69_eq :
    closedCollarFiber word [LColor.p, LColor.b, LColor.p, LColor.r] = fiber69 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.p, LColor.r]
  exact hfast.trans fiber69_keyed_eq

theorem cert69_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.p, LColor.r] = [] := by
  have hnil : fiber69 = [] := by
    decide
  exact fiber69_eq.trans hnil

theorem cert69_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert69_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
