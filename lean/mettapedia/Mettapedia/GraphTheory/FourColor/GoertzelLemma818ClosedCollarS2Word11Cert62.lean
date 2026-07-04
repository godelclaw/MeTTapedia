import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word11

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast62 : List TauState :=
  [stateAt 161, stateAt 169, stateAt 177, stateAt 185]

theorem keyedLast62_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.p, LColor.p]) =
      keyedLast62 := by
  decide

def fiber62OuterChunks : List (List (List TauState)) :=
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

def fiber62 : List (List TauState) :=
  fiber62OuterChunks.flatten

theorem fiber62_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 0 []) =
      listGetD fiber62OuterChunks 0 [] := by
  decide

theorem fiber62_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 1 []) =
      listGetD fiber62OuterChunks 1 [] := by
  decide

theorem fiber62_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 2 []) =
      listGetD fiber62OuterChunks 2 [] := by
  decide

theorem fiber62_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 3 []) =
      listGetD fiber62OuterChunks 3 [] := by
  decide

theorem fiber62_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 4 []) =
      listGetD fiber62OuterChunks 4 [] := by
  decide

theorem fiber62_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 5 []) =
      listGetD fiber62OuterChunks 5 [] := by
  decide

theorem fiber62_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 6 []) =
      listGetD fiber62OuterChunks 6 [] := by
  decide

theorem fiber62_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 7 []) =
      listGetD fiber62OuterChunks 7 [] := by
  decide

theorem fiber62_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 8 []) =
      listGetD fiber62OuterChunks 8 [] := by
  decide

theorem fiber62_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 9 []) =
      listGetD fiber62OuterChunks 9 [] := by
  decide

theorem fiber62_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 10 []) =
      listGetD fiber62OuterChunks 10 [] := by
  decide

theorem fiber62_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks 11 []) =
      listGetD fiber62OuterChunks 11 [] := by
  decide

theorem fiber62_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast62
        (listGetD tauStateChunks idx []) =
      listGetD fiber62OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber62_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber62_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber62_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber62_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber62_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber62_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber62_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber62_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber62_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber62_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber62_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber62_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber62_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast62 =
      fiber62 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast62 tauStateChunks fiber62OuterChunks
    tauStateChunks_eq (by rfl) fiber62_outer_get
  simpa [fiber62] using h

theorem fiber62_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.p, LColor.p] = fiber62 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.p, LColor.p] keyedLast62_eq
  exact hfrom.trans fiber62_keyedFrom_eq

theorem fiber62_eq :
    closedCollarFiber word [LColor.p, LColor.r, LColor.p, LColor.p] = fiber62 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.mirror TauOrient.mirror TauOrient.mirror [LColor.p, LColor.r, LColor.p, LColor.p]
  exact hfast.trans fiber62_keyed_eq

theorem cert62_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.p, LColor.p] = [] := by
  have hnil : fiber62 = [] := by
    decide
  exact fiber62_eq.trans hnil

theorem cert62_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert62_empty


end GoertzelLemma818ClosedCollarS2Word11
end Mettapedia.GraphTheory.FourColor
