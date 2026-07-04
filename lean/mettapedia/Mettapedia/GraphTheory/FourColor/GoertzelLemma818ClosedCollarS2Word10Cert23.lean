import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word10Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word10

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast23 : List TauState :=
  [stateAt 37, stateAt 45, stateAt 53, stateAt 61]

theorem keyedLast23_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.b, LColor.p]) =
      keyedLast23 := by
  decide

def fiber23OuterChunks : List (List (List TauState)) :=
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

def fiber23 : List (List TauState) :=
  fiber23OuterChunks.flatten

theorem fiber23_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 0 []) =
      listGetD fiber23OuterChunks 0 [] := by
  decide

theorem fiber23_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 1 []) =
      listGetD fiber23OuterChunks 1 [] := by
  decide

theorem fiber23_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 2 []) =
      listGetD fiber23OuterChunks 2 [] := by
  decide

theorem fiber23_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 3 []) =
      listGetD fiber23OuterChunks 3 [] := by
  decide

theorem fiber23_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 4 []) =
      listGetD fiber23OuterChunks 4 [] := by
  decide

theorem fiber23_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 5 []) =
      listGetD fiber23OuterChunks 5 [] := by
  decide

theorem fiber23_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 6 []) =
      listGetD fiber23OuterChunks 6 [] := by
  decide

theorem fiber23_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 7 []) =
      listGetD fiber23OuterChunks 7 [] := by
  decide

theorem fiber23_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 8 []) =
      listGetD fiber23OuterChunks 8 [] := by
  decide

theorem fiber23_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 9 []) =
      listGetD fiber23OuterChunks 9 [] := by
  decide

theorem fiber23_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 10 []) =
      listGetD fiber23OuterChunks 10 [] := by
  decide

theorem fiber23_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks 11 []) =
      listGetD fiber23OuterChunks 11 [] := by
  decide

theorem fiber23_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast23
        (listGetD tauStateChunks idx []) =
      listGetD fiber23OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber23_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber23_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber23_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber23_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber23_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber23_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber23_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber23_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber23_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber23_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber23_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber23_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber23_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast23 =
      fiber23 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast23 tauStateChunks fiber23OuterChunks
    tauStateChunks_eq (by rfl) fiber23_outer_get
  simpa [fiber23] using h

theorem fiber23_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.b, LColor.p] = fiber23 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.b, LColor.p] keyedLast23_eq
  exact hfrom.trans fiber23_keyedFrom_eq

theorem fiber23_eq :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.p] = fiber23 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.normal [LColor.r, LColor.p, LColor.b, LColor.p]
  exact hfast.trans fiber23_keyed_eq

theorem cert23_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.p] = [] := by
  have hnil : fiber23 = [] := by
    decide
  exact fiber23_eq.trans hnil

theorem cert23_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert23_empty


end GoertzelLemma818ClosedCollarS2Word10
end Mettapedia.GraphTheory.FourColor
