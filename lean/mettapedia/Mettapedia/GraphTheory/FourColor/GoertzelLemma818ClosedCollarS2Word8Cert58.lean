import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast58 : List TauState :=
  [stateAt 162, stateAt 170, stateAt 178, stateAt 186]

theorem keyedLast58_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.b, LColor.b]) =
      keyedLast58 := by
  decide

def fiber58OuterChunks : List (List (List TauState)) :=
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

def fiber58 : List (List TauState) :=
  fiber58OuterChunks.flatten

theorem fiber58_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 0 []) =
      listGetD fiber58OuterChunks 0 [] := by
  decide

theorem fiber58_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 1 []) =
      listGetD fiber58OuterChunks 1 [] := by
  decide

theorem fiber58_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 2 []) =
      listGetD fiber58OuterChunks 2 [] := by
  decide

theorem fiber58_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 3 []) =
      listGetD fiber58OuterChunks 3 [] := by
  decide

theorem fiber58_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 4 []) =
      listGetD fiber58OuterChunks 4 [] := by
  decide

theorem fiber58_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 5 []) =
      listGetD fiber58OuterChunks 5 [] := by
  decide

theorem fiber58_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 6 []) =
      listGetD fiber58OuterChunks 6 [] := by
  decide

theorem fiber58_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 7 []) =
      listGetD fiber58OuterChunks 7 [] := by
  decide

theorem fiber58_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 8 []) =
      listGetD fiber58OuterChunks 8 [] := by
  decide

theorem fiber58_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 9 []) =
      listGetD fiber58OuterChunks 9 [] := by
  decide

theorem fiber58_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 10 []) =
      listGetD fiber58OuterChunks 10 [] := by
  decide

theorem fiber58_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks 11 []) =
      listGetD fiber58OuterChunks 11 [] := by
  decide

theorem fiber58_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast58
        (listGetD tauStateChunks idx []) =
      listGetD fiber58OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber58_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber58_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber58_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber58_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber58_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber58_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber58_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber58_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber58_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber58_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber58_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber58_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber58_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast58 =
      fiber58 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast58 tauStateChunks fiber58OuterChunks
    tauStateChunks_eq (by rfl) fiber58_outer_get
  simpa [fiber58] using h

theorem fiber58_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.b, LColor.b] = fiber58 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.b, LColor.b] keyedLast58_eq
  exact hfrom.trans fiber58_keyedFrom_eq

theorem fiber58_eq :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.b] = fiber58 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.p, LColor.r, LColor.b, LColor.b]
  exact hfast.trans fiber58_keyed_eq

theorem cert58_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.b] = [] := by
  have hnil : fiber58 = [] := by
    decide
  exact fiber58_eq.trans hnil

theorem cert58_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert58_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
