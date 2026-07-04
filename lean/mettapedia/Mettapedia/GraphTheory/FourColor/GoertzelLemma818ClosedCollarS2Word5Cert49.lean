import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast49 : List TauState :=
  [stateAt 68, stateAt 76, stateAt 84, stateAt 92]

theorem keyedLast49_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.b, LColor.b]) =
      keyedLast49 := by
  decide

def fiber49OuterChunks : List (List (List TauState)) :=
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

def fiber49 : List (List TauState) :=
  fiber49OuterChunks.flatten

theorem fiber49_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 0 []) =
      listGetD fiber49OuterChunks 0 [] := by
  decide

theorem fiber49_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 1 []) =
      listGetD fiber49OuterChunks 1 [] := by
  decide

theorem fiber49_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 2 []) =
      listGetD fiber49OuterChunks 2 [] := by
  decide

theorem fiber49_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 3 []) =
      listGetD fiber49OuterChunks 3 [] := by
  decide

theorem fiber49_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 4 []) =
      listGetD fiber49OuterChunks 4 [] := by
  decide

theorem fiber49_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 5 []) =
      listGetD fiber49OuterChunks 5 [] := by
  decide

theorem fiber49_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 6 []) =
      listGetD fiber49OuterChunks 6 [] := by
  decide

theorem fiber49_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 7 []) =
      listGetD fiber49OuterChunks 7 [] := by
  decide

theorem fiber49_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 8 []) =
      listGetD fiber49OuterChunks 8 [] := by
  decide

theorem fiber49_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 9 []) =
      listGetD fiber49OuterChunks 9 [] := by
  decide

theorem fiber49_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 10 []) =
      listGetD fiber49OuterChunks 10 [] := by
  decide

theorem fiber49_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks 11 []) =
      listGetD fiber49OuterChunks 11 [] := by
  decide

theorem fiber49_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast49
        (listGetD tauStateChunks idx []) =
      listGetD fiber49OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber49_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber49_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber49_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber49_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber49_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber49_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber49_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber49_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber49_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber49_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber49_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber49_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber49_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast49 =
      fiber49 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast49 tauStateChunks fiber49OuterChunks
    tauStateChunks_eq (by rfl) fiber49_outer_get
  simpa [fiber49] using h

theorem fiber49_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.b, LColor.b] = fiber49 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.b, LColor.b] keyedLast49_eq
  exact hfrom.trans fiber49_keyedFrom_eq

theorem fiber49_eq :
    closedCollarFiber word [LColor.b, LColor.p, LColor.b, LColor.b] = fiber49 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.b, LColor.b]
  exact hfast.trans fiber49_keyed_eq

theorem cert49_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.b, LColor.b] = [] := by
  have hnil : fiber49 = [] := by
    decide
  exact fiber49_eq.trans hnil

theorem cert49_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert49_empty


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
