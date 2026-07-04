import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word6Base

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word6

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast63 : List TauState :=
  [stateAt 131, stateAt 139, stateAt 147, stateAt 155]

theorem keyedLast63_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.r, LColor.r]) =
      keyedLast63 := by
  decide

def fiber63OuterChunks : List (List (List TauState)) :=
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

def fiber63 : List (List TauState) :=
  fiber63OuterChunks.flatten

theorem fiber63_outer0 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 0 []) =
      listGetD fiber63OuterChunks 0 [] := by
  decide

theorem fiber63_outer1 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 1 []) =
      listGetD fiber63OuterChunks 1 [] := by
  decide

theorem fiber63_outer2 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 2 []) =
      listGetD fiber63OuterChunks 2 [] := by
  decide

theorem fiber63_outer3 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 3 []) =
      listGetD fiber63OuterChunks 3 [] := by
  decide

theorem fiber63_outer4 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 4 []) =
      listGetD fiber63OuterChunks 4 [] := by
  decide

theorem fiber63_outer5 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 5 []) =
      listGetD fiber63OuterChunks 5 [] := by
  decide

theorem fiber63_outer6 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 6 []) =
      listGetD fiber63OuterChunks 6 [] := by
  decide

theorem fiber63_outer7 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 7 []) =
      listGetD fiber63OuterChunks 7 [] := by
  decide

theorem fiber63_outer8 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 8 []) =
      listGetD fiber63OuterChunks 8 [] := by
  decide

theorem fiber63_outer9 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 9 []) =
      listGetD fiber63OuterChunks 9 [] := by
  decide

theorem fiber63_outer10 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 10 []) =
      listGetD fiber63OuterChunks 10 [] := by
  decide

theorem fiber63_outer11 :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks 11 []) =
      listGetD fiber63OuterChunks 11 [] := by
  decide

theorem fiber63_outer_get
    (idx : Nat) (hidx : idx < tauStateChunks.length) :
    closedCollarFiber3KeyedFromFirsts word keyedLast63
        (listGetD tauStateChunks idx []) =
      listGetD fiber63OuterChunks idx [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : idx = 0
  · subst idx
    simpa using fiber63_outer0
  by_cases h1 : idx = 1
  · subst idx
    simpa using fiber63_outer1
  by_cases h2 : idx = 2
  · subst idx
    simpa using fiber63_outer2
  by_cases h3 : idx = 3
  · subst idx
    simpa using fiber63_outer3
  by_cases h4 : idx = 4
  · subst idx
    simpa using fiber63_outer4
  by_cases h5 : idx = 5
  · subst idx
    simpa using fiber63_outer5
  by_cases h6 : idx = 6
  · subst idx
    simpa using fiber63_outer6
  by_cases h7 : idx = 7
  · subst idx
    simpa using fiber63_outer7
  by_cases h8 : idx = 8
  · subst idx
    simpa using fiber63_outer8
  by_cases h9 : idx = 9
  · subst idx
    simpa using fiber63_outer9
  by_cases h10 : idx = 10
  · subst idx
    simpa using fiber63_outer10
  by_cases h11 : idx = 11
  · subst idx
    simpa using fiber63_outer11
  · have hbound : idx < 12 := by
      simpa [hlen] using hidx
    omega

theorem fiber63_keyedFrom_eq :
    closedCollarFiber3KeyedFrom word keyedLast63 =
      fiber63 := by
  have h := closedCollarFiber3KeyedFrom_eq_chunks
    word keyedLast63 tauStateChunks fiber63OuterChunks
    tauStateChunks_eq (by rfl) fiber63_outer_get
  simpa [fiber63] using h

theorem fiber63_keyed_eq :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.r, LColor.r] = fiber63 := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.r, LColor.r] keyedLast63_eq
  exact hfrom.trans fiber63_keyedFrom_eq

theorem fiber63_eq :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.r] = fiber63 := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.mirror TauOrient.normal [LColor.p, LColor.b, LColor.r, LColor.r]
  exact hfast.trans fiber63_keyed_eq

theorem cert63_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.r] = [] := by
  have hnil : fiber63 = [] := by
    decide
  exact fiber63_eq.trans hnil

theorem cert63_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert63_empty


end GoertzelLemma818ClosedCollarS2Word6
end Mettapedia.GraphTheory.FourColor
