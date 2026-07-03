import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.14: real `chainLKRInAudit` endpoints

This module proves the one-gadget normal and mirror words against the actual
`chainLKRInAudit` definition.  The proof is chunked by fixed input key, so no
single theorem asks Lean to reduce the whole all-input audit at once.
-/

namespace GoertzelLemma814RealAudit

open GoertzelLemma814

def realFiberAuditAt (orients : List TauOrient) (i : Nat) : Bool :=
  let statesList := allChainStates orients
  chainFiberConnected orients
    (chainFiberFrom orients statesList (listGetD colorAssignments4 i []))

def realFiberChunkAudit (orients : List TauOrient) (start len : Nat) : Bool :=
  (List.range len).all fun k => realFiberAuditAt orients (start + k)

def range81By9 : List Nat :=
  (List.range 9).map (fun k => 0 + k) ++
  (List.range 9).map (fun k => 9 + k) ++
  (List.range 9).map (fun k => 18 + k) ++
  (List.range 9).map (fun k => 27 + k) ++
  (List.range 9).map (fun k => 36 + k) ++
  (List.range 9).map (fun k => 45 + k) ++
  (List.range 9).map (fun k => 54 + k) ++
  (List.range 9).map (fun k => 63 + k) ++
  (List.range 9).map (fun k => 72 + k)

def allBy9 (p : Nat → Bool) : Bool :=
  (List.range 9).all (fun k => p (0 + k)) &&
  (List.range 9).all (fun k => p (9 + k)) &&
  (List.range 9).all (fun k => p (18 + k)) &&
  (List.range 9).all (fun k => p (27 + k)) &&
  (List.range 9).all (fun k => p (36 + k)) &&
  (List.range 9).all (fun k => p (45 + k)) &&
  (List.range 9).all (fun k => p (54 + k)) &&
  (List.range 9).all (fun k => p (63 + k)) &&
  (List.range 9).all (fun k => p (72 + k))

theorem colorAssignments4_all_eq_range (p : List LColor → Bool) :
    colorAssignments4.all p =
      (List.range 81).all fun i => p (listGetD colorAssignments4 i []) := by
  have h : colorAssignments4 =
      (List.range 81).map (fun i => listGetD colorAssignments4 i []) := by
    decide
  conv_lhs => rw [h]
  rfl

theorem range81By9_eq_range81 : range81By9 = List.range 81 := by
  decide

theorem range81_all_eq_chunks (p : Nat → Bool) :
    (List.range 81).all p = allBy9 p := by
  rw [← range81By9_eq_range81]
  simp only [range81By9, allBy9, List.all_append, List.all_map, Function.comp_def]

theorem normalRealFiberChunk_0_9_ok :
    realFiberChunkAudit [TauOrient.normal] 0 9 = true := by
  decide

theorem normalRealFiberChunk_9_9_ok :
    realFiberChunkAudit [TauOrient.normal] 9 9 = true := by
  decide

theorem normalRealFiberChunk_18_9_ok :
    realFiberChunkAudit [TauOrient.normal] 18 9 = true := by
  decide

theorem normalRealFiberChunk_27_9_ok :
    realFiberChunkAudit [TauOrient.normal] 27 9 = true := by
  decide

theorem normalRealFiberChunk_36_9_ok :
    realFiberChunkAudit [TauOrient.normal] 36 9 = true := by
  decide

theorem normalRealFiberChunk_45_9_ok :
    realFiberChunkAudit [TauOrient.normal] 45 9 = true := by
  decide

theorem normalRealFiberChunk_54_9_ok :
    realFiberChunkAudit [TauOrient.normal] 54 9 = true := by
  decide

theorem normalRealFiberChunk_63_9_ok :
    realFiberChunkAudit [TauOrient.normal] 63 9 = true := by
  decide

theorem normalRealFiberChunk_72_9_ok :
    realFiberChunkAudit [TauOrient.normal] 72 9 = true := by
  decide

theorem normalRealAllBy9_ok :
    allBy9 (realFiberAuditAt [TauOrient.normal]) = true := by
  change (realFiberChunkAudit [TauOrient.normal] 0 9 &&
    realFiberChunkAudit [TauOrient.normal] 9 9 &&
    realFiberChunkAudit [TauOrient.normal] 18 9 &&
    realFiberChunkAudit [TauOrient.normal] 27 9 &&
    realFiberChunkAudit [TauOrient.normal] 36 9 &&
    realFiberChunkAudit [TauOrient.normal] 45 9 &&
    realFiberChunkAudit [TauOrient.normal] 54 9 &&
    realFiberChunkAudit [TauOrient.normal] 63 9 &&
    realFiberChunkAudit [TauOrient.normal] 72 9) = true
  simp [normalRealFiberChunk_0_9_ok,
    normalRealFiberChunk_9_9_ok,
    normalRealFiberChunk_18_9_ok,
    normalRealFiberChunk_27_9_ok,
    normalRealFiberChunk_36_9_ok,
    normalRealFiberChunk_45_9_ok,
    normalRealFiberChunk_54_9_ok,
    normalRealFiberChunk_63_9_ok,
    normalRealFiberChunk_72_9_ok]

theorem mirrorRealFiberChunk_0_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 0 9 = true := by
  decide

theorem mirrorRealFiberChunk_9_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 9 9 = true := by
  decide

theorem mirrorRealFiberChunk_18_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 18 9 = true := by
  decide

theorem mirrorRealFiberChunk_27_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 27 9 = true := by
  decide

theorem mirrorRealFiberChunk_36_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 36 9 = true := by
  decide

theorem mirrorRealFiberChunk_45_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 45 9 = true := by
  decide

theorem mirrorRealFiberChunk_54_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 54 9 = true := by
  decide

theorem mirrorRealFiberChunk_63_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 63 9 = true := by
  decide

theorem mirrorRealFiberChunk_72_9_ok :
    realFiberChunkAudit [TauOrient.mirror] 72 9 = true := by
  decide

theorem mirrorRealAllBy9_ok :
    allBy9 (realFiberAuditAt [TauOrient.mirror]) = true := by
  change (realFiberChunkAudit [TauOrient.mirror] 0 9 &&
    realFiberChunkAudit [TauOrient.mirror] 9 9 &&
    realFiberChunkAudit [TauOrient.mirror] 18 9 &&
    realFiberChunkAudit [TauOrient.mirror] 27 9 &&
    realFiberChunkAudit [TauOrient.mirror] 36 9 &&
    realFiberChunkAudit [TauOrient.mirror] 45 9 &&
    realFiberChunkAudit [TauOrient.mirror] 54 9 &&
    realFiberChunkAudit [TauOrient.mirror] 63 9 &&
    realFiberChunkAudit [TauOrient.mirror] 72 9) = true
  simp [mirrorRealFiberChunk_0_9_ok,
    mirrorRealFiberChunk_9_9_ok,
    mirrorRealFiberChunk_18_9_ok,
    mirrorRealFiberChunk_27_9_ok,
    mirrorRealFiberChunk_36_9_ok,
    mirrorRealFiberChunk_45_9_ok,
    mirrorRealFiberChunk_54_9_ok,
    mirrorRealFiberChunk_63_9_ok,
    mirrorRealFiberChunk_72_9_ok]

theorem tauSingleNormalChainLKRInAudit_ok :
    chainLKRInAudit [TauOrient.normal] = true := by
  change ((allChainStates [TauOrient.normal]).all
      (compatibleChainStates [TauOrient.normal]) &&
    colorAssignments4.all (fun key =>
      chainFiberConnected [TauOrient.normal]
        (chainFiberFrom [TauOrient.normal]
          (allChainStates [TauOrient.normal]) key))) = true
  rw [colorAssignments4_all_eq_range]
  rw [range81_all_eq_chunks]
  change (tauSingleNormalChainStatesCompatibleCheck &&
    allBy9 (realFiberAuditAt [TauOrient.normal])) = true
  simp [tauSingleNormalChainStatesCompatibleCheck_ok, normalRealAllBy9_ok]

theorem tauSingleMirrorChainLKRInAudit_ok :
    chainLKRInAudit [TauOrient.mirror] = true := by
  change ((allChainStates [TauOrient.mirror]).all
      (compatibleChainStates [TauOrient.mirror]) &&
    colorAssignments4.all (fun key =>
      chainFiberConnected [TauOrient.mirror]
        (chainFiberFrom [TauOrient.mirror]
          (allChainStates [TauOrient.mirror]) key))) = true
  rw [colorAssignments4_all_eq_range]
  rw [range81_all_eq_chunks]
  change (tauSingleChainStatesCompatibleCheck TauOrient.mirror &&
    allBy9 (realFiberAuditAt [TauOrient.mirror])) = true
  simp [tauSingleMirrorChainStatesCompatibleCheck_ok, mirrorRealAllBy9_ok]

theorem tauSingleChainLKRInAudit_ok (orient : TauOrient) :
    chainLKRInAudit [orient] = true := by
  cases orient
  · exact tauSingleNormalChainLKRInAudit_ok
  · exact tauSingleMirrorChainLKRInAudit_ok

end GoertzelLemma814RealAudit

end Mettapedia.GraphTheory.FourColor
