import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast32 : List TauState :=
  [stateAt 163, stateAt 171, stateAt 179, stateAt 187]

theorem keyedLast32_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.b, LColor.p]) =
      keyedLast32 := by
  decide

def fiber32OuterChunks : List (List (List TauState)) :=
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

def fiber32 : List (List TauState) :=
  fiber32OuterChunks.flatten

theorem fiber32_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 0 []) =
      listGetD fiber32OuterChunks 0 [] := by
  decide

theorem fiber32_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 1 []) =
      listGetD fiber32OuterChunks 1 [] := by
  decide

theorem fiber32_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 2 []) =
      listGetD fiber32OuterChunks 2 [] := by
  decide

theorem fiber32_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 3 []) =
      listGetD fiber32OuterChunks 3 [] := by
  decide

theorem fiber32_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 4 []) =
      listGetD fiber32OuterChunks 4 [] := by
  decide

theorem fiber32_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 5 []) =
      listGetD fiber32OuterChunks 5 [] := by
  decide

theorem fiber32_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 6 []) =
      listGetD fiber32OuterChunks 6 [] := by
  decide

theorem fiber32_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 7 []) =
      listGetD fiber32OuterChunks 7 [] := by
  decide

theorem fiber32_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 8 []) =
      listGetD fiber32OuterChunks 8 [] := by
  decide

theorem fiber32_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 9 []) =
      listGetD fiber32OuterChunks 9 [] := by
  decide

theorem fiber32_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 10 []) =
      listGetD fiber32OuterChunks 10 [] := by
  decide

theorem fiber32_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks 11 []) =
      listGetD fiber32OuterChunks 11 [] := by
  decide

theorem fiber32_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast32
        (listGetD tauStateChunks idx []) =
      listGetD fiber32OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber32_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber32_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber32_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber32_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber32_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber32_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber32_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber32_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber32_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber32_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber32_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber32_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber32_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast32 =
      fiber32 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast32 tauStateChunks fiber32OuterChunks
    tauStateChunks_eq (by rfl) fiber32_outer_get
  simpa [fiber32] using h

theorem fiber32_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.b, LColor.p] = fiber32 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.b, LColor.p] keyedLast32_eq
  exact hfrom.trans fiber32_keyedFrom_eq

theorem fiber32_eq :
    closedCollarFiber word [LColor.b, LColor.r, LColor.b, LColor.p] = fiber32 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.b, LColor.r, LColor.b, LColor.p]
  exact hfast.trans fiber32_keyed_eq

theorem cert32_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.b, LColor.p] = [] := by
  have hnil : fiber32 = [] := by
    decide
  exact fiber32_eq.trans hnil

theorem cert32_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert32_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
