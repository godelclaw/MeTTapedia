import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast43 : List TauState :=
  [stateAt 68, stateAt 76, stateAt 84, stateAt 92]

theorem keyedLast43_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.p, LColor.b]) =
      keyedLast43 := by
  decide

def fiber43OuterChunks : List (List (List TauState)) :=
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

def fiber43 : List (List TauState) :=
  fiber43OuterChunks.flatten

theorem fiber43_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 0 []) =
      listGetD fiber43OuterChunks 0 [] := by
  decide

theorem fiber43_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 1 []) =
      listGetD fiber43OuterChunks 1 [] := by
  decide

theorem fiber43_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 2 []) =
      listGetD fiber43OuterChunks 2 [] := by
  decide

theorem fiber43_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 3 []) =
      listGetD fiber43OuterChunks 3 [] := by
  decide

theorem fiber43_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 4 []) =
      listGetD fiber43OuterChunks 4 [] := by
  decide

theorem fiber43_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 5 []) =
      listGetD fiber43OuterChunks 5 [] := by
  decide

theorem fiber43_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 6 []) =
      listGetD fiber43OuterChunks 6 [] := by
  decide

theorem fiber43_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 7 []) =
      listGetD fiber43OuterChunks 7 [] := by
  decide

theorem fiber43_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 8 []) =
      listGetD fiber43OuterChunks 8 [] := by
  decide

theorem fiber43_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 9 []) =
      listGetD fiber43OuterChunks 9 [] := by
  decide

theorem fiber43_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 10 []) =
      listGetD fiber43OuterChunks 10 [] := by
  decide

theorem fiber43_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks 11 []) =
      listGetD fiber43OuterChunks 11 [] := by
  decide

theorem fiber43_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast43
        (listGetD tauStateChunks idx []) =
      listGetD fiber43OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber43_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber43_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber43_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber43_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber43_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber43_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber43_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber43_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber43_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber43_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber43_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber43_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber43_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast43 =
      fiber43 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast43 tauStateChunks fiber43OuterChunks
    tauStateChunks_eq (by rfl) fiber43_outer_get
  simpa [fiber43] using h

theorem fiber43_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.p, LColor.b] = fiber43 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.p, LColor.b] keyedLast43_eq
  exact hfrom.trans fiber43_keyedFrom_eq

theorem fiber43_eq :
    closedCollarFiber word [LColor.b, LColor.b, LColor.p, LColor.b] = fiber43 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.b, LColor.b, LColor.p, LColor.b]
  exact hfast.trans fiber43_keyed_eq

theorem cert43_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.p, LColor.b] = [] := by
  have hnil : fiber43 = [] := by
    decide
  exact fiber43_eq.trans hnil

theorem cert43_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert43_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
