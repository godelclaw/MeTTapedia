import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast35 : List TauState :=
  [stateAt 96, stateAt 104, stateAt 112, stateAt 120]

theorem keyedLast35_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.p, LColor.p]) =
      keyedLast35 := by
  decide

def fiber35OuterChunks : List (List (List TauState)) :=
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

def fiber35 : List (List TauState) :=
  fiber35OuterChunks.flatten

theorem fiber35_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 0 []) =
      listGetD fiber35OuterChunks 0 [] := by
  decide

theorem fiber35_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 1 []) =
      listGetD fiber35OuterChunks 1 [] := by
  decide

theorem fiber35_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 2 []) =
      listGetD fiber35OuterChunks 2 [] := by
  decide

theorem fiber35_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 3 []) =
      listGetD fiber35OuterChunks 3 [] := by
  decide

theorem fiber35_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 4 []) =
      listGetD fiber35OuterChunks 4 [] := by
  decide

theorem fiber35_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 5 []) =
      listGetD fiber35OuterChunks 5 [] := by
  decide

theorem fiber35_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 6 []) =
      listGetD fiber35OuterChunks 6 [] := by
  decide

theorem fiber35_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 7 []) =
      listGetD fiber35OuterChunks 7 [] := by
  decide

theorem fiber35_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 8 []) =
      listGetD fiber35OuterChunks 8 [] := by
  decide

theorem fiber35_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 9 []) =
      listGetD fiber35OuterChunks 9 [] := by
  decide

theorem fiber35_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 10 []) =
      listGetD fiber35OuterChunks 10 [] := by
  decide

theorem fiber35_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks 11 []) =
      listGetD fiber35OuterChunks 11 [] := by
  decide

theorem fiber35_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast35
        (listGetD tauStateChunks idx []) =
      listGetD fiber35OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber35_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber35_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber35_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber35_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber35_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber35_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber35_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber35_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber35_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber35_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber35_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber35_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber35_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast35 =
      fiber35 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast35 tauStateChunks fiber35OuterChunks
    tauStateChunks_eq (by rfl) fiber35_outer_get
  simpa [fiber35] using h

theorem fiber35_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.p, LColor.p] = fiber35 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.p, LColor.p] keyedLast35_eq
  exact hfrom.trans fiber35_keyedFrom_eq

theorem fiber35_eq :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.p] = fiber35 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.b, LColor.r, LColor.p, LColor.p]
  exact hfast.trans fiber35_keyed_eq

theorem cert35_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.p] = [] := by
  have hnil : fiber35 = [] := by
    decide
  exact fiber35_eq.trans hnil

theorem cert35_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert35_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
