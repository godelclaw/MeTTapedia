import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word8

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast77 : List TauState :=
  [stateAt 129, stateAt 137, stateAt 145, stateAt 153]

theorem keyedLast77_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.b, LColor.p]) =
      keyedLast77 := by
  decide

def fiber77OuterChunks : List (List (List TauState)) :=
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

def fiber77 : List (List TauState) :=
  fiber77OuterChunks.flatten

theorem fiber77_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 0 []) =
      listGetD fiber77OuterChunks 0 [] := by
  decide

theorem fiber77_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 1 []) =
      listGetD fiber77OuterChunks 1 [] := by
  decide

theorem fiber77_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 2 []) =
      listGetD fiber77OuterChunks 2 [] := by
  decide

theorem fiber77_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 3 []) =
      listGetD fiber77OuterChunks 3 [] := by
  decide

theorem fiber77_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 4 []) =
      listGetD fiber77OuterChunks 4 [] := by
  decide

theorem fiber77_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 5 []) =
      listGetD fiber77OuterChunks 5 [] := by
  decide

theorem fiber77_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 6 []) =
      listGetD fiber77OuterChunks 6 [] := by
  decide

theorem fiber77_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 7 []) =
      listGetD fiber77OuterChunks 7 [] := by
  decide

theorem fiber77_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 8 []) =
      listGetD fiber77OuterChunks 8 [] := by
  decide

theorem fiber77_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 9 []) =
      listGetD fiber77OuterChunks 9 [] := by
  decide

theorem fiber77_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 10 []) =
      listGetD fiber77OuterChunks 10 [] := by
  decide

theorem fiber77_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks 11 []) =
      listGetD fiber77OuterChunks 11 [] := by
  decide

theorem fiber77_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast77
        (listGetD tauStateChunks idx []) =
      listGetD fiber77OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber77_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber77_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber77_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber77_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber77_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber77_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber77_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber77_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber77_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber77_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber77_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber77_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber77_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast77 =
      fiber77 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast77 tauStateChunks fiber77OuterChunks
    tauStateChunks_eq (by rfl) fiber77_outer_get
  simpa [fiber77] using h

theorem fiber77_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.b, LColor.p] = fiber77 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.b, LColor.p] keyedLast77_eq
  exact hfrom.trans fiber77_keyedFrom_eq

theorem fiber77_eq :
    closedCollarFiber word [LColor.p, LColor.p, LColor.b, LColor.p] = fiber77 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.normal [LColor.p, LColor.p, LColor.b, LColor.p]
  exact hfast.trans fiber77_keyed_eq

theorem cert77_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.b, LColor.p] = [] := by
  have hnil : fiber77 = [] := by
    decide
  exact fiber77_eq.trans hnil

theorem cert77_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert77_empty


end GoertzelLemma818ClosedCollarS2Word8
end Mettapedia.GraphTheory.FourColor
