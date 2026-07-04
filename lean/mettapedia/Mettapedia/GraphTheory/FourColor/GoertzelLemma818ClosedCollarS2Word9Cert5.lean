import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word9

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast5 : List TauState :=
  [stateAt 131, stateAt 139, stateAt 147, stateAt 155]

theorem keyedLast5_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.b, LColor.p]) =
      keyedLast5 := by
  decide

def fiber5OuterChunks : List (List (List TauState)) :=
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

def fiber5 : List (List TauState) :=
  fiber5OuterChunks.flatten

theorem fiber5_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 0 []) =
      listGetD fiber5OuterChunks 0 [] := by
  decide

theorem fiber5_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 1 []) =
      listGetD fiber5OuterChunks 1 [] := by
  decide

theorem fiber5_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 2 []) =
      listGetD fiber5OuterChunks 2 [] := by
  decide

theorem fiber5_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 3 []) =
      listGetD fiber5OuterChunks 3 [] := by
  decide

theorem fiber5_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 4 []) =
      listGetD fiber5OuterChunks 4 [] := by
  decide

theorem fiber5_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 5 []) =
      listGetD fiber5OuterChunks 5 [] := by
  decide

theorem fiber5_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 6 []) =
      listGetD fiber5OuterChunks 6 [] := by
  decide

theorem fiber5_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 7 []) =
      listGetD fiber5OuterChunks 7 [] := by
  decide

theorem fiber5_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 8 []) =
      listGetD fiber5OuterChunks 8 [] := by
  decide

theorem fiber5_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 9 []) =
      listGetD fiber5OuterChunks 9 [] := by
  decide

theorem fiber5_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 10 []) =
      listGetD fiber5OuterChunks 10 [] := by
  decide

theorem fiber5_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks 11 []) =
      listGetD fiber5OuterChunks 11 [] := by
  decide

theorem fiber5_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast5
        (listGetD tauStateChunks idx []) =
      listGetD fiber5OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber5_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber5_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber5_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber5_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber5_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber5_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber5_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber5_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber5_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber5_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber5_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber5_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber5_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast5 =
      fiber5 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast5 tauStateChunks fiber5OuterChunks
    tauStateChunks_eq (by rfl) fiber5_outer_get
  simpa [fiber5] using h

theorem fiber5_keyed_eq :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.b, LColor.p] = fiber5 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.b, LColor.p] keyedLast5_eq
  exact hfrom.trans fiber5_keyedFrom_eq

theorem fiber5_eq :
    closedCollarFiber word [LColor.r, LColor.r, LColor.b, LColor.p] = fiber5 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.b, LColor.p]
  exact hfast.trans fiber5_keyed_eq

theorem cert5_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.b, LColor.p] = [] := by
  have hnil : fiber5 = [] := by
    decide
  exact fiber5_eq.trans hnil

theorem cert5_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert5_empty


end GoertzelLemma818ClosedCollarS2Word9
end Mettapedia.GraphTheory.FourColor
