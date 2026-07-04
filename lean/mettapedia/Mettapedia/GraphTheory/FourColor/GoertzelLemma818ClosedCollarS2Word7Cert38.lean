import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word7

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast38 : List TauState :=
  [stateAt 162, stateAt 170, stateAt 178, stateAt 186]

theorem keyedLast38_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.r, LColor.p]) =
      keyedLast38 := by
  decide

def fiber38OuterChunks : List (List (List TauState)) :=
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

def fiber38 : List (List TauState) :=
  fiber38OuterChunks.flatten

theorem fiber38_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 0 []) =
      listGetD fiber38OuterChunks 0 [] := by
  decide

theorem fiber38_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 1 []) =
      listGetD fiber38OuterChunks 1 [] := by
  decide

theorem fiber38_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 2 []) =
      listGetD fiber38OuterChunks 2 [] := by
  decide

theorem fiber38_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 3 []) =
      listGetD fiber38OuterChunks 3 [] := by
  decide

theorem fiber38_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 4 []) =
      listGetD fiber38OuterChunks 4 [] := by
  decide

theorem fiber38_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 5 []) =
      listGetD fiber38OuterChunks 5 [] := by
  decide

theorem fiber38_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 6 []) =
      listGetD fiber38OuterChunks 6 [] := by
  decide

theorem fiber38_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 7 []) =
      listGetD fiber38OuterChunks 7 [] := by
  decide

theorem fiber38_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 8 []) =
      listGetD fiber38OuterChunks 8 [] := by
  decide

theorem fiber38_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 9 []) =
      listGetD fiber38OuterChunks 9 [] := by
  decide

theorem fiber38_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 10 []) =
      listGetD fiber38OuterChunks 10 [] := by
  decide

theorem fiber38_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks 11 []) =
      listGetD fiber38OuterChunks 11 [] := by
  decide

theorem fiber38_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast38
        (listGetD tauStateChunks idx []) =
      listGetD fiber38OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber38_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber38_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber38_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber38_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber38_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber38_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber38_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber38_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber38_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber38_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber38_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber38_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber38_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast38 =
      fiber38 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast38 tauStateChunks fiber38OuterChunks
    tauStateChunks_eq (by rfl) fiber38_outer_get
  simpa [fiber38] using h

theorem fiber38_keyed_eq :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.r, LColor.p] = fiber38 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.r, LColor.p] keyedLast38_eq
  exact hfrom.trans fiber38_keyedFrom_eq

theorem fiber38_eq :
    closedCollarFiber word [LColor.b, LColor.b, LColor.r, LColor.p] = fiber38 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.mirror [LColor.b, LColor.b, LColor.r, LColor.p]
  exact hfast.trans fiber38_keyed_eq

theorem cert38_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.r, LColor.p] = [] := by
  have hnil : fiber38 = [] := by
    decide
  exact fiber38_eq.trans hnil

theorem cert38_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert38_empty


end GoertzelLemma818ClosedCollarS2Word7
end Mettapedia.GraphTheory.FourColor
