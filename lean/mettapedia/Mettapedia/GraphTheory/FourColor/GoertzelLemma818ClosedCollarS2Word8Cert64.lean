import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast64 : List TauState :=
  [stateAt 163, stateAt 171, stateAt 179, stateAt 187]

theorem keyedLast64_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.r, LColor.b]) =
      keyedLast64 := by
  decide

def fiber64OuterChunks : List (List (List TauState)) :=
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

def fiber64 : List (List TauState) :=
  fiber64OuterChunks.flatten

theorem fiber64_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 0 []) =
      listGetD fiber64OuterChunks 0 [] := by
  decide

theorem fiber64_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 1 []) =
      listGetD fiber64OuterChunks 1 [] := by
  decide

theorem fiber64_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 2 []) =
      listGetD fiber64OuterChunks 2 [] := by
  decide

theorem fiber64_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 3 []) =
      listGetD fiber64OuterChunks 3 [] := by
  decide

theorem fiber64_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 4 []) =
      listGetD fiber64OuterChunks 4 [] := by
  decide

theorem fiber64_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 5 []) =
      listGetD fiber64OuterChunks 5 [] := by
  decide

theorem fiber64_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 6 []) =
      listGetD fiber64OuterChunks 6 [] := by
  decide

theorem fiber64_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 7 []) =
      listGetD fiber64OuterChunks 7 [] := by
  decide

theorem fiber64_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 8 []) =
      listGetD fiber64OuterChunks 8 [] := by
  decide

theorem fiber64_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 9 []) =
      listGetD fiber64OuterChunks 9 [] := by
  decide

theorem fiber64_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 10 []) =
      listGetD fiber64OuterChunks 10 [] := by
  decide

theorem fiber64_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks 11 []) =
      listGetD fiber64OuterChunks 11 [] := by
  decide

theorem fiber64_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast64
        (listGetD tauStateChunks idx []) =
      listGetD fiber64OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber64_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber64_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber64_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber64_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber64_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber64_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber64_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber64_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber64_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber64_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber64_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber64_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber64_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast64 =
      fiber64 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast64 tauStateChunks fiber64OuterChunks
    tauStateChunks_eq (by rfl) fiber64_outer_get
  simpa [fiber64] using h

theorem fiber64_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.r, LColor.b] = fiber64 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.r, LColor.b] keyedLast64_eq
  exact hfrom.trans fiber64_keyedFrom_eq

theorem fiber64_eq :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.b] = fiber64 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.p, LColor.b, LColor.r, LColor.b]
  exact hfast.trans fiber64_keyed_eq

theorem cert64_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.b] = [] := by
  have hnil : fiber64 = [] := by
    decide
  exact fiber64_eq.trans hnil

theorem cert64_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert64_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
