import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast47 : List TauState :=
  [stateAt 97, stateAt 105, stateAt 113, stateAt 121]

theorem keyedLast47_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.r, LColor.p]) =
      keyedLast47 := by
  decide

def fiber47OuterChunks : List (List (List TauState)) :=
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

def fiber47 : List (List TauState) :=
  fiber47OuterChunks.flatten

theorem fiber47_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 0 []) =
      listGetD fiber47OuterChunks 0 [] := by
  decide

theorem fiber47_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 1 []) =
      listGetD fiber47OuterChunks 1 [] := by
  decide

theorem fiber47_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 2 []) =
      listGetD fiber47OuterChunks 2 [] := by
  decide

theorem fiber47_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 3 []) =
      listGetD fiber47OuterChunks 3 [] := by
  decide

theorem fiber47_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 4 []) =
      listGetD fiber47OuterChunks 4 [] := by
  decide

theorem fiber47_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 5 []) =
      listGetD fiber47OuterChunks 5 [] := by
  decide

theorem fiber47_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 6 []) =
      listGetD fiber47OuterChunks 6 [] := by
  decide

theorem fiber47_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 7 []) =
      listGetD fiber47OuterChunks 7 [] := by
  decide

theorem fiber47_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 8 []) =
      listGetD fiber47OuterChunks 8 [] := by
  decide

theorem fiber47_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 9 []) =
      listGetD fiber47OuterChunks 9 [] := by
  decide

theorem fiber47_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 10 []) =
      listGetD fiber47OuterChunks 10 [] := by
  decide

theorem fiber47_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks 11 []) =
      listGetD fiber47OuterChunks 11 [] := by
  decide

theorem fiber47_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast47
        (listGetD tauStateChunks idx []) =
      listGetD fiber47OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber47_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber47_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber47_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber47_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber47_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber47_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber47_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber47_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber47_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber47_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber47_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber47_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber47_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast47 =
      fiber47 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast47 tauStateChunks fiber47OuterChunks
    tauStateChunks_eq (by rfl) fiber47_outer_get
  simpa [fiber47] using h

theorem fiber47_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.r, LColor.p] = fiber47 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.r, LColor.p] keyedLast47_eq
  exact hfrom.trans fiber47_keyedFrom_eq

theorem fiber47_eq :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.p] = fiber47 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.b, LColor.p, LColor.r, LColor.p]
  exact hfast.trans fiber47_keyed_eq

theorem cert47_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.p] = [] := by
  have hnil : fiber47 = [] := by
    decide
  exact fiber47_eq.trans hnil

theorem cert47_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert47_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
