import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionDisjointCircuit

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Two positive coherent line-graph paths meeting at one edge can always
be joined coherently. If their junctions use opposite endpoints, append the
paths. If they use the same endpoint, contract the common line vertex and
use the resulting triangle shortcut. -/
theorem exists_isPath_isPrimalCoherent_length_le_of_append_isPath
    {first middle last : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle last)
    (hleftPath : left.IsPath) (hrightPath : right.IsPath)
    (hleftCoherent : left.IsPrimalCoherent)
    (hrightCoherent : right.IsPrimalCoherent)
    (hleftPositive : 0 < left.length)
    (hrightPositive : 0 < right.length)
    (happendPath : (left.append right).IsPath) :
    ∃ joined : G.lineGraph.Walk first last,
      joined.IsPath ∧ joined.IsPrimalCoherent ∧
        0 < joined.length ∧
        joined.length ≤ (left.append right).length ∧
        joined.support ⊆ (left.append right).support := by
  let leftLast : Fin left.length :=
    ⟨left.length - 1,
      Nat.sub_lt hleftPositive Nat.zero_lt_one⟩
  let rightFirst : Fin right.length := ⟨0, hrightPositive⟩
  by_cases hseam :
      left.lineGraphJunctionAt leftLast ≠
        right.lineGraphJunctionAt rightFirst
  · refine ⟨left.append right, happendPath, ?_, by simp; omega,
      le_rfl, fun _ hedge ↦ hedge⟩
    apply hleftCoherent.append hrightCoherent
    intro hleftPositive' hrightPositive'
    simpa only [Subsingleton.elim hleftPositive' hleftPositive,
      Subsingleton.elim hrightPositive' hrightPositive,
      leftLast, rightFirst] using hseam
  · have hseamEq :
        left.lineGraphJunctionAt leftLast =
          right.lineGraphJunctionAt rightFirst :=
      not_ne_iff.mp hseam
    have hrightNotNil : ¬right.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hrightPositive
    have happendSupportDisjoint :
        left.support.Disjoint right.support.tail := by
      have hnodup := happendPath.support_nodup
      rw [SimpleGraph.Walk.support_append, List.nodup_append'] at hnodup
      exact hnodup.2.2
    have hpreviousNe : left.penultimate ≠ right.snd := by
      intro heq
      have hleftMem : left.penultimate ∈ left.support :=
        left.getVert_mem_support (left.length - 1)
      have hrightMem : right.snd ∈ right.support.tail :=
        right.getVert_mem_tail_support hrightNotNil (by omega)
      exact (List.disjoint_left.mp happendSupportDisjoint)
        hleftMem (by simpa only [heq] using hrightMem)
    let shortcutAdj : G.lineGraph.Adj left.penultimate right.snd := by
      apply Mettapedia.GraphTheory.FourColor.lineGraph_adj_of_common_vertex_of_ne
        (vertex := left.lineGraphJunctionAt leftLast)
      · simpa only [leftLast] using
          left.lineGraphJunctionAt_mem_left leftLast
      · rw [hseamEq]
        simpa only [rightFirst, Nat.zero_add] using
          right.lineGraphJunctionAt_mem_right rightFirst
      · exact hpreviousNe
    let rightShortcut := SimpleGraph.Walk.cons shortcutAdj right.tail
    let joined := left.dropLast.append rightShortcut
    have hshortcutCommonRight :
        SimpleGraph.lineGraphCommonVertex shortcutAdj =
          right.lineGraphJunctionAt rightFirst := by
      symm
      apply SimpleGraph.lineGraphCommonVertex_unique
      · rw [← hseamEq]
        simpa only [leftLast] using
          left.lineGraphJunctionAt_mem_left leftLast
      · simpa only [rightFirst, Nat.zero_add] using
          right.lineGraphJunctionAt_mem_right rightFirst
    have hrightShortcutPath : rightShortcut.IsPath := by
      dsimp only [rightShortcut]
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hrightPath.tail, ?_⟩
      intro hmem
      have hmem' : left.penultimate ∈ right.support.tail := by
        simpa only [right.support_tail_of_not_nil hrightNotNil] using hmem
      exact (List.disjoint_left.mp happendSupportDisjoint)
        (left.getVert_mem_support (left.length - 1)) hmem'
    have hleftDropPath : left.dropLast.IsPath :=
      SimpleGraph.Walk.isPath_of_isSubwalk
        (SimpleGraph.Walk.isSubwalk_rfl left).dropLast hleftPath
    have hjoinedSupportDisjoint :
        left.dropLast.support.Disjoint rightShortcut.support.tail := by
      rw [List.disjoint_left]
      intro edge hleftDrop hrightShortcut
      have hleftSupport : edge ∈ left.support :=
        (SimpleGraph.Walk.isSubwalk_rfl left).dropLast.support_subset
          hleftDrop
      have hrightTailSupport : edge ∈ right.tail.support := by
        simpa only [rightShortcut, SimpleGraph.Walk.support_cons,
          List.tail_cons] using hrightShortcut
      have hrightSupport : edge ∈ right.support.tail := by
        simpa only [right.support_tail_of_not_nil hrightNotNil] using
          hrightTailSupport
      exact (List.disjoint_left.mp happendSupportDisjoint)
        hleftSupport hrightSupport
    have hjoinedPath : joined.IsPath := by
      dsimp only [joined]
      rw [SimpleGraph.Walk.isPath_def,
        SimpleGraph.Walk.support_append, List.nodup_append']
      exact ⟨hleftDropPath.support_nodup,
        hrightShortcutPath.support_nodup.tail,
        hjoinedSupportDisjoint⟩
    have hrightShortcutCoherent : rightShortcut.IsPrimalCoherent := by
      dsimp only [rightShortcut]
      apply hrightCoherent.tail.cons_of_firstJunction_ne shortcutAdj
      intro htailPositive
      have hrightLength :=
        SimpleGraph.Walk.length_tail_add_one hrightNotNil
      have hrightStep :
          right.lineGraphJunctionAt rightFirst ≠
            right.lineGraphJunctionAt ⟨1, by omega⟩ := by
        have hraw := hrightCoherent 0 (by omega)
        simpa only [rightFirst] using hraw
      have htailJunction :=
        right.lineGraphJunctionAt_tail ⟨0, htailPositive⟩
      intro heq
      apply hrightStep
      exact hshortcutCommonRight.symm.trans
        (heq.trans htailJunction)
    have hjoinedCoherent : joined.IsPrimalCoherent := by
      dsimp only [joined]
      apply hleftCoherent.dropLast.append hrightShortcutCoherent
      intro hleftDropPositive _hrightShortcutPositive
      let leftBeforeLast : Fin left.length :=
        ⟨left.length - 2, by
          rw [SimpleGraph.Walk.length_dropLast] at hleftDropPositive
          omega⟩
      let leftDropLast : Fin left.dropLast.length :=
        ⟨left.dropLast.length - 1,
          Nat.sub_lt hleftDropPositive Nat.zero_lt_one⟩
      have hleftStep :
          left.lineGraphJunctionAt leftBeforeLast ≠
            left.lineGraphJunctionAt leftLast := by
        have hraw := hleftCoherent (left.length - 2) (by
          rw [SimpleGraph.Walk.length_dropLast] at hleftDropPositive
          omega)
        intro heq
        apply hraw
        let rawFirst : Fin left.length :=
          ⟨left.length - 2, by
            rw [SimpleGraph.Walk.length_dropLast] at hleftDropPositive
            omega⟩
        let rawSecond : Fin left.length :=
          ⟨left.length - 2 + 1, by
            rw [SimpleGraph.Walk.length_dropLast] at hleftDropPositive
            omega⟩
        have hfirstPosition : rawFirst = leftBeforeLast := by
          apply Fin.ext
          rfl
        have hsecondPosition : rawSecond = leftLast := by
          apply Fin.ext
          dsimp only [rawSecond, leftLast]
          rw [SimpleGraph.Walk.length_dropLast] at hleftDropPositive
          omega
        exact (congrArg left.lineGraphJunctionAt hfirstPosition).trans
          (heq.trans
            (congrArg left.lineGraphJunctionAt hsecondPosition.symm))
      have hdrop := left.lineGraphJunctionAt_dropLast leftDropLast
      let leftDropLifted : Fin left.length :=
        ⟨leftDropLast.val, by
          have hposition : leftDropLast.val < left.length - 1 := by
            simpa only [SimpleGraph.Walk.length_dropLast] using
              leftDropLast.isLt
          omega⟩
      have hdropLifted :
          left.dropLast.lineGraphJunctionAt leftDropLast =
            left.lineGraphJunctionAt leftDropLifted := by
        simpa only [leftDropLifted] using hdrop
      have hdropPosition : leftDropLifted = leftBeforeLast := by
        apply Fin.ext
        dsimp only [leftDropLifted, leftDropLast, leftBeforeLast]
        rw [SimpleGraph.Walk.length_dropLast]
        omega
      have hdropExact :
          left.dropLast.lineGraphJunctionAt leftDropLast =
            left.lineGraphJunctionAt leftBeforeLast :=
        hdropLifted.trans
          (congrArg left.lineGraphJunctionAt hdropPosition)
      have hshortcutFirst :=
        SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
          shortcutAdj right.tail
      have hshortcutCommonLeft :
          SimpleGraph.lineGraphCommonVertex shortcutAdj =
            left.lineGraphJunctionAt leftLast :=
        hshortcutCommonRight.trans hseamEq.symm
      change left.dropLast.lineGraphJunctionAt leftDropLast ≠
        rightShortcut.lineGraphJunctionAt
          ⟨0, by simp [rightShortcut]⟩
      intro heq
      apply hleftStep
      exact hdropExact.symm.trans
        (heq.trans (hshortcutFirst.trans hshortcutCommonLeft))
    have hfirstLast : first ≠ last := by
      intro heq
      have hnil : (left.append right).Nil :=
        happendPath.nil_iff_eq.mpr heq
      have hzero := hnil.length_eq_zero
      rw [SimpleGraph.Walk.length_append] at hzero
      omega
    have hjoinedPositive : 0 < joined.length := by
      apply SimpleGraph.Walk.not_nil_iff_lt_length.mp
      exact SimpleGraph.Walk.not_nil_of_ne hfirstLast
    have hjoinedLength :
        joined.length ≤ (left.append right).length := by
      have hrightLength :=
        SimpleGraph.Walk.length_tail_add_one hrightNotNil
      dsimp only [joined, rightShortcut]
      rw [SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_dropLast,
        SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_append]
      omega
    have hjoinedSupportSubset :
        joined.support ⊆ (left.append right).support := by
      intro edge hedge
      dsimp only [joined] at hedge
      rw [SimpleGraph.Walk.support_append, List.mem_append] at hedge
      rw [SimpleGraph.Walk.support_append, List.mem_append]
      rcases hedge with hleftDrop | hrightShortcut
      · exact Or.inl
          ((SimpleGraph.Walk.isSubwalk_rfl left).dropLast.support_subset
            hleftDrop)
      · have hrightTailSupport : edge ∈ right.tail.support := by
          simpa only [rightShortcut, SimpleGraph.Walk.support_cons,
            List.tail_cons] using hrightShortcut
        exact Or.inr (by
          simpa only [right.support_tail_of_not_nil hrightNotNil] using
            hrightTailSupport)
    exact ⟨joined, hjoinedPath, hjoinedCoherent,
      hjoinedPositive, hjoinedLength, hjoinedSupportSubset⟩

end SimpleGraph.Walk
