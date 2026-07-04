import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast3 : List TauState :=
  [stateAt 39, stateAt 47, stateAt 55, stateAt 63]

theorem keyedLast3_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.b, LColor.r]) =
      keyedLast3 := by
  decide

def fiber3OuterChunks : List (List (List TauState)) :=
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

def fiber3 : List (List TauState) :=
  fiber3OuterChunks.flatten

theorem fiber3_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 0 []) =
      listGetD fiber3OuterChunks 0 [] := by
  decide

theorem fiber3_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 1 []) =
      listGetD fiber3OuterChunks 1 [] := by
  decide

theorem fiber3_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 2 []) =
      listGetD fiber3OuterChunks 2 [] := by
  decide

theorem fiber3_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 3 []) =
      listGetD fiber3OuterChunks 3 [] := by
  decide

theorem fiber3_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 4 []) =
      listGetD fiber3OuterChunks 4 [] := by
  decide

theorem fiber3_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 5 []) =
      listGetD fiber3OuterChunks 5 [] := by
  decide

theorem fiber3_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 6 []) =
      listGetD fiber3OuterChunks 6 [] := by
  decide

theorem fiber3_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 7 []) =
      listGetD fiber3OuterChunks 7 [] := by
  decide

theorem fiber3_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 8 []) =
      listGetD fiber3OuterChunks 8 [] := by
  decide

theorem fiber3_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 9 []) =
      listGetD fiber3OuterChunks 9 [] := by
  decide

theorem fiber3_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 10 []) =
      listGetD fiber3OuterChunks 10 [] := by
  decide

theorem fiber3_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks 11 []) =
      listGetD fiber3OuterChunks 11 [] := by
  decide

theorem fiber3_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast3
        (listGetD tauStateChunks idx []) =
      listGetD fiber3OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber3_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber3_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber3_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber3_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber3_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber3_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber3_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber3_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber3_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber3_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber3_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber3_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber3_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast3 =
      fiber3 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast3 tauStateChunks fiber3OuterChunks
    tauStateChunks_eq (by rfl) fiber3_outer_get
  simpa [fiber3] using h

theorem fiber3_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.b, LColor.r] = fiber3 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.b, LColor.r] keyedLast3_eq
  exact hfrom.trans fiber3_keyedFrom_eq

theorem fiber3_eq :
    closedCollarFiber word [LColor.r, LColor.r, LColor.b, LColor.r] = fiber3 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.r, LColor.r, LColor.b, LColor.r]
  exact hfast.trans fiber3_keyed_eq

theorem cert3_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.b, LColor.r] = [] := by
  have hnil : fiber3 = [] := by
    decide
  exact fiber3_eq.trans hnil

theorem cert3_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert3_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
