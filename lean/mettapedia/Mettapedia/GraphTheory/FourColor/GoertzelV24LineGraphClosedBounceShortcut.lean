import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionBounceCircuit

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V}

noncomputable section

/-- The direct line-graph edge obtained by suppressing a bounced common
vertex between two positive arcs. -/
def closedBounceAdj
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    G.lineGraph.Adj left.penultimate right.snd := by
  apply Mettapedia.GraphTheory.FourColor.lineGraph_adj_of_common_vertex_of_ne
    (vertex := left.lineGraphJunctionAt
      ⟨left.length - 1, by omega⟩)
  · exact left.lineGraphJunctionAt_mem_left ⟨left.length - 1, by omega⟩
  · rw [hbounce]
    exact right.lineGraphJunctionAt_mem_right ⟨0, hrightPositive⟩
  · exact hne

/-- Replace the first vertex of the returning arc by the predecessor of the
bounced common vertex. -/
def closedBounceReturn
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    G.lineGraph.Walk left.penultimate first :=
  SimpleGraph.Walk.cons
    (closedBounceAdj left right hleftTwo hrightPositive hbounce hne)
    right.tail

/-- Suppress a bounced common line vertex and close along the shortened
first arc. -/
def closedBounceShortcut
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    G.lineGraph.Walk first first :=
  left.dropLast.append
    (closedBounceReturn left right hleftTwo hrightPositive hbounce hne)

theorem closedBounceAdj_commonVertex_right
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    SimpleGraph.lineGraphCommonVertex
        (closedBounceAdj left right hleftTwo hrightPositive hbounce hne) =
      right.lineGraphJunctionAt ⟨0, hrightPositive⟩ := by
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · rw [← hbounce]
    exact left.lineGraphJunctionAt_mem_left ⟨left.length - 1, by omega⟩
  · exact right.lineGraphJunctionAt_mem_right ⟨0, hrightPositive⟩

@[simp] theorem closedBounceReturn_length
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    (closedBounceReturn left right hleftTwo hrightPositive hbounce hne).length =
      right.length := by
  have hrightNotNil : ¬right.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hrightPositive
  rw [closedBounceReturn, SimpleGraph.Walk.length_cons]
  have hlength := SimpleGraph.Walk.length_tail_add_one hrightNotNil
  omega

@[simp] theorem closedBounceShortcut_length_add_one
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    (closedBounceShortcut left right hleftTwo hrightPositive
        hbounce hne).length + 1 =
      (left.append right).length := by
  rw [closedBounceShortcut, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_dropLast, closedBounceReturn_length,
    SimpleGraph.Walk.length_append]
  omega

theorem closedBounceReturn_isPrimalCoherent
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd)
    (hrightCoherent : right.IsPrimalCoherent) :
    (closedBounceReturn left right hleftTwo hrightPositive
      hbounce hne).IsPrimalCoherent := by
  let shortcutAdj := closedBounceAdj left right hleftTwo
    hrightPositive hbounce hne
  change (SimpleGraph.Walk.cons shortcutAdj right.tail).IsPrimalCoherent
  apply hrightCoherent.tail.cons_of_firstJunction_ne shortcutAdj
  intro htailPositive
  have hrightNotNil : ¬right.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hrightPositive
  have hrightLength := SimpleGraph.Walk.length_tail_add_one hrightNotNil
  have hrightStep :
      right.lineGraphJunctionAt ⟨0, hrightPositive⟩ ≠
        right.lineGraphJunctionAt ⟨1, by omega⟩ := by
    exact hrightCoherent 0 (by omega)
  have htailJunction :=
    right.lineGraphJunctionAt_tail ⟨0, htailPositive⟩
  have hshortcutCommon := closedBounceAdj_commonVertex_right
    left right hleftTwo hrightPositive hbounce hne
  intro heq
  apply hrightStep
  exact hshortcutCommon.symm.trans (heq.trans htailJunction)

theorem closedBounceNewSeam_ne
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd)
    (hleftCoherent : left.IsPrimalCoherent) :
    left.dropLast.lineGraphJunctionAt
        ⟨left.dropLast.length - 1, by
          rw [SimpleGraph.Walk.length_dropLast]
          omega⟩ ≠
      (closedBounceReturn left right hleftTwo hrightPositive
        hbounce hne).lineGraphJunctionAt
          ⟨0, by simp [hrightPositive]⟩ := by
  let leftBeforeLast : Fin left.length := ⟨left.length - 2, by omega⟩
  let leftLast : Fin left.length := ⟨left.length - 1, by omega⟩
  let leftDropLast : Fin left.dropLast.length :=
    ⟨left.dropLast.length - 1, by
      rw [SimpleGraph.Walk.length_dropLast]
      omega⟩
  have hleftStep :
      left.lineGraphJunctionAt leftBeforeLast ≠
        left.lineGraphJunctionAt leftLast := by
    have hraw := hleftCoherent (left.length - 2) (by omega)
    intro heq
    apply hraw
    let rawFirst : Fin left.length :=
      ⟨left.length - 2, by omega⟩
    let rawSecond : Fin left.length :=
      ⟨left.length - 2 + 1, by omega⟩
    have hfirstPosition : rawFirst = leftBeforeLast := by
      apply Fin.ext
      rfl
    have hsecondPosition : rawSecond = leftLast := by
      apply Fin.ext
      dsimp only [rawSecond, leftLast]
      omega
    exact (congrArg left.lineGraphJunctionAt hfirstPosition).trans
      (heq.trans
        (congrArg left.lineGraphJunctionAt hsecondPosition.symm))
  have hdrop := left.lineGraphJunctionAt_dropLast leftDropLast
  let leftDropLifted : Fin left.length :=
    ⟨leftDropLast.val, by
      have hposition : leftDropLast.val < left.length - 1 := by
        simpa only [SimpleGraph.Walk.length_dropLast] using leftDropLast.isLt
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
    hdropLifted.trans (congrArg left.lineGraphJunctionAt hdropPosition)
  have hshortcutFirst :=
    SimpleGraph.Walk.lineGraphJunctionAt_cons_zero
      (closedBounceAdj left right hleftTwo hrightPositive hbounce hne)
      right.tail
  have hshortcutCommonLeft :
      SimpleGraph.lineGraphCommonVertex
          (closedBounceAdj left right hleftTwo hrightPositive hbounce hne) =
        left.lineGraphJunctionAt leftLast := by
    exact (closedBounceAdj_commonVertex_right left right hleftTwo
      hrightPositive hbounce hne).trans hbounce.symm
  change left.dropLast.lineGraphJunctionAt leftDropLast ≠
    (closedBounceReturn left right hleftTwo hrightPositive
      hbounce hne).lineGraphJunctionAt ⟨0, by simp [hrightPositive]⟩
  intro heq
  apply hleftStep
  exact hdropExact.symm.trans
    (heq.trans (hshortcutFirst.trans hshortcutCommonLeft))

theorem closedBounceReturn_lastJunction
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd) :
    (closedBounceReturn left right hleftTwo hrightPositive
        hbounce hne).lineGraphJunctionAt
          ⟨(closedBounceReturn left right hleftTwo hrightPositive
              hbounce hne).length - 1, by simp [hrightPositive]⟩ =
      right.lineGraphJunctionAt
        ⟨right.length - 1, by omega⟩ := by
  exact SimpleGraph.Walk.lineGraphJunctionAt_cons_tail_last
    right hrightPositive
    (closedBounceAdj left right hleftTwo hrightPositive hbounce hne)
    (closedBounceAdj_commonVertex_right left right hleftTwo
      hrightPositive hbounce hne)

theorem closedBounceShortcut_isPrimalCoherentClosed
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, hrightPositive⟩)
    (hne : left.penultimate ≠ right.snd)
    (hleftCoherent : left.IsPrimalCoherent)
    (hrightCoherent : right.IsPrimalCoherent)
    (hclosing :
      right.lineGraphJunctionAt
          ⟨right.length - 1, by omega⟩ ≠
        left.lineGraphJunctionAt ⟨0, by omega⟩) :
    (closedBounceShortcut left right hleftTwo hrightPositive
      hbounce hne).IsPrimalCoherentClosed := by
  have hleftDropPositive : 0 < left.dropLast.length := by
    rw [SimpleGraph.Walk.length_dropLast]
    omega
  have hreturnPositive : 0 <
      (closedBounceReturn left right hleftTwo hrightPositive
        hbounce hne).length := by
    simp [hrightPositive]
  have hreturnCoherent := closedBounceReturn_isPrimalCoherent
    left right hleftTwo hrightPositive hbounce hne hrightCoherent
  have hnewSeam := closedBounceNewSeam_ne
    left right hleftTwo hrightPositive hbounce hne hleftCoherent
  have hreturnLast := closedBounceReturn_lastJunction
    left right hleftTwo hrightPositive hbounce hne
  have hleftFirst := left.lineGraphJunctionAt_dropLast
    ⟨0, hleftDropPositive⟩
  have hnewClosing :
      (closedBounceReturn left right hleftTwo hrightPositive
          hbounce hne).lineGraphJunctionAt
            ⟨(closedBounceReturn left right hleftTwo hrightPositive
                hbounce hne).length - 1,
              Nat.sub_lt hreturnPositive Nat.zero_lt_one⟩ ≠
        left.dropLast.lineGraphJunctionAt ⟨0, hleftDropPositive⟩ := by
    intro heq
    apply hclosing
    exact hreturnLast.symm.trans (heq.trans hleftFirst)
  change (left.dropLast.append
    (closedBounceReturn left right hleftTwo hrightPositive
      hbounce hne)).IsPrimalCoherentClosed
  apply SimpleGraph.Walk.IsPrimalCoherent.append_isPrimalCoherentClosed
    hleftCoherent.dropLast hreturnCoherent hleftDropPositive
      hreturnPositive hnewSeam hnewClosing

theorem penultimate_ne_snd_of_tail_disjoint
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightPositive : 0 < right.length)
    (hdisjoint : left.support.tail.Disjoint right.support.tail) :
    left.penultimate ≠ right.snd := by
  have hleftNotNil : ¬left.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hrightNotNil : ¬right.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact hrightPositive
  have hleftMem : left.penultimate ∈ left.support.tail :=
    left.getVert_mem_tail_support hleftNotNil (by omega)
  have hrightMem : right.snd ∈ right.support.tail :=
    right.snd_mem_tail_support hrightNotNil
  intro heq
  exact (List.disjoint_left.mp hdisjoint) hleftMem (heq ▸ hrightMem)

theorem closedBounceReturn_penultimate
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightTwo : 2 ≤ right.length)
    (hbounce :
      left.lineGraphJunctionAt
          ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, by omega⟩)
    (hne : left.penultimate ≠ right.snd) :
    (closedBounceReturn left right hleftTwo (by omega)
      hbounce hne).penultimate = right.penultimate := by
  let shortcutAdj := closedBounceAdj left right hleftTwo
    (by omega) hbounce hne
  have hrightNotNil : ¬right.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have htailNotNil : ¬right.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have hlength := SimpleGraph.Walk.length_tail_add_one hrightNotNil
    omega
  change (SimpleGraph.Walk.cons shortcutAdj right.tail).penultimate =
    right.penultimate
  rw [SimpleGraph.Walk.penultimate_cons_of_not_nil
    shortcutAdj right.tail htailNotNil]
  change right.tail.getVert (right.tail.length - 1) =
    right.getVert (right.length - 1)
  rw [SimpleGraph.Walk.getVert_tail]
  have hlength := SimpleGraph.Walk.length_tail_add_one hrightNotNil
  congr 1
  omega

theorem dropLast_snd
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (hleftTwo : 2 ≤ left.length) :
    left.dropLast.snd = left.snd := by
  change left.dropLast.getVert 1 = left.getVert 1
  simp only [SimpleGraph.Walk.dropLast, SimpleGraph.Walk.take_getVert]
  rw [Nat.min_eq_right]
  omega

/-- If both endpoint splices bounce, suppress them successively. The first
suppression makes its replacement splice coherent, so the rotated second
suppression closes coherently. -/
theorem exists_isPrimalCoherentClosed_of_two_bounces
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightTwo : 2 ≤ right.length)
    (hleftCoherent : left.IsPrimalCoherent)
    (hrightCoherent : right.IsPrimalCoherent)
    (hdisjoint : left.support.tail.Disjoint right.support.tail)
    (hfirstBounce :
      left.lineGraphJunctionAt ⟨left.length - 1, by omega⟩ =
        right.lineGraphJunctionAt ⟨0, by omega⟩)
    (hsecondBounce :
      right.lineGraphJunctionAt ⟨right.length - 1, by omega⟩ =
        left.lineGraphJunctionAt ⟨0, by omega⟩) :
    ∃ (edge : G.edgeSet) (shortcut : G.lineGraph.Walk edge edge),
      0 < shortcut.length ∧ shortcut.IsPrimalCoherentClosed ∧
        shortcut.length + 2 = (left.append right).length := by
  have hfirstNe := penultimate_ne_snd_of_tail_disjoint
    left right hleftTwo (by omega) hdisjoint
  let alteredRight := closedBounceReturn left right hleftTwo
    (by omega) hfirstBounce hfirstNe
  let shortenedLeft := left.dropLast
  have halteredTwo : 2 ≤ alteredRight.length := by
    dsimp only [alteredRight]
    rw [closedBounceReturn_length]
    exact hrightTwo
  have hshortenedPositive : 0 < shortenedLeft.length := by
    dsimp only [shortenedLeft]
    rw [SimpleGraph.Walk.length_dropLast]
    omega
  have halteredCoherent : alteredRight.IsPrimalCoherent := by
    dsimp only [alteredRight]
    exact closedBounceReturn_isPrimalCoherent left right hleftTwo
      (by omega) hfirstBounce hfirstNe hrightCoherent
  have hshortenedCoherent : shortenedLeft.IsPrimalCoherent := by
    exact hleftCoherent.dropLast
  have halteredLast := closedBounceReturn_lastJunction
    left right hleftTwo (by omega) hfirstBounce hfirstNe
  have hshortenedFirst := left.lineGraphJunctionAt_dropLast
    ⟨0, hshortenedPositive⟩
  have hrotatedBounce :
      alteredRight.lineGraphJunctionAt
          ⟨alteredRight.length - 1, by omega⟩ =
        shortenedLeft.lineGraphJunctionAt ⟨0, hshortenedPositive⟩ := by
    exact halteredLast.trans (hsecondBounce.trans hshortenedFirst.symm)
  have hoppositeNe : right.penultimate ≠ left.snd :=
    penultimate_ne_snd_of_tail_disjoint right left hrightTwo
      (by omega) hdisjoint.symm
  have hrotatedNe : alteredRight.penultimate ≠ shortenedLeft.snd := by
    intro heq
    apply hoppositeNe
    exact (closedBounceReturn_penultimate left right hleftTwo hrightTwo
      hfirstBounce hfirstNe).symm.trans
        (heq.trans (dropLast_snd left hleftTwo))
  have hnewClosing :
      shortenedLeft.lineGraphJunctionAt
          ⟨shortenedLeft.length - 1, by omega⟩ ≠
        alteredRight.lineGraphJunctionAt ⟨0, by omega⟩ := by
    dsimp only [shortenedLeft, alteredRight]
    exact closedBounceNewSeam_ne left right hleftTwo (by omega)
      hfirstBounce hfirstNe hleftCoherent
  let shortcut := closedBounceShortcut alteredRight shortenedLeft
    halteredTwo hshortenedPositive hrotatedBounce hrotatedNe
  refine ⟨left.penultimate, shortcut, ?_, ?_, ?_⟩
  · dsimp only [shortcut]
    have hadd := closedBounceShortcut_length_add_one alteredRight
      shortenedLeft halteredTwo hshortenedPositive hrotatedBounce hrotatedNe
    have hrightLength := closedBounceReturn_length left right hleftTwo
      (by omega) hfirstBounce hfirstNe
    rw [SimpleGraph.Walk.length_append] at hadd
    dsimp only [alteredRight, shortenedLeft] at hadd ⊢
    rw [hrightLength, SimpleGraph.Walk.length_dropLast] at hadd
    omega
  · dsimp only [shortcut]
    exact closedBounceShortcut_isPrimalCoherentClosed alteredRight
      shortenedLeft halteredTwo hshortenedPositive hrotatedBounce hrotatedNe
      halteredCoherent hshortenedCoherent hnewClosing
  · dsimp only [shortcut]
    have houter := closedBounceShortcut_length_add_one alteredRight
      shortenedLeft halteredTwo hshortenedPositive hrotatedBounce hrotatedNe
    have hinner := closedBounceReturn_length left right hleftTwo
      (by omega) hfirstBounce hfirstNe
    rw [SimpleGraph.Walk.length_append] at houter ⊢
    dsimp only [alteredRight, shortenedLeft] at houter ⊢
    rw [hinner, SimpleGraph.Walk.length_dropLast] at houter
    omega

/-- Two internally coherent arcs with disjoint support tails can always be
closed primal-coherently: append across coherent splices and suppress each
bounced splice otherwise. -/
theorem exists_isPrimalCoherentClosed_length_le_of_two_arcs
    {first middle : G.edgeSet}
    (left : G.lineGraph.Walk first middle)
    (right : G.lineGraph.Walk middle first)
    (hleftTwo : 2 ≤ left.length)
    (hrightTwo : 2 ≤ right.length)
    (hleftCoherent : left.IsPrimalCoherent)
    (hrightCoherent : right.IsPrimalCoherent)
    (hdisjoint : left.support.tail.Disjoint right.support.tail) :
    ∃ (edge : G.edgeSet) (shortcut : G.lineGraph.Walk edge edge),
      0 < shortcut.length ∧ shortcut.IsPrimalCoherentClosed ∧
        shortcut.length ≤ (left.append right).length := by
  let leftLast : Fin left.length := ⟨left.length - 1, by omega⟩
  let rightFirst : Fin right.length := ⟨0, by omega⟩
  let rightLast : Fin right.length := ⟨right.length - 1, by omega⟩
  let leftFirst : Fin left.length := ⟨0, by omega⟩
  by_cases hfirst :
      left.lineGraphJunctionAt leftLast ≠
        right.lineGraphJunctionAt rightFirst
  · by_cases hsecond :
        right.lineGraphJunctionAt rightLast ≠
          left.lineGraphJunctionAt leftFirst
    · refine ⟨first, left.append right, by simp; omega, ?_, le_rfl⟩
      exact hleftCoherent.append_isPrimalCoherentClosed hrightCoherent
        (by omega) (by omega) hfirst hsecond
    · have hsecondEq := not_ne_iff.mp hsecond
      have hne := penultimate_ne_snd_of_tail_disjoint right left
        hrightTwo (by omega) hdisjoint.symm
      let shortcut := closedBounceShortcut right left hrightTwo
        (by omega) hsecondEq hne
      refine ⟨middle, shortcut, ?_, ?_, ?_⟩
      · dsimp only [shortcut]
        have hadd := closedBounceShortcut_length_add_one right left
          hrightTwo (by omega) hsecondEq hne
        rw [SimpleGraph.Walk.length_append] at hadd
        omega
      · dsimp only [shortcut]
        exact closedBounceShortcut_isPrimalCoherentClosed right left
          hrightTwo (by omega) hsecondEq hne hrightCoherent
          hleftCoherent hfirst
      · dsimp only [shortcut]
        have hadd := closedBounceShortcut_length_add_one right left
          hrightTwo (by omega) hsecondEq hne
        rw [SimpleGraph.Walk.length_append] at hadd ⊢
        omega
  · have hfirstEq := not_ne_iff.mp hfirst
    by_cases hsecond :
        right.lineGraphJunctionAt rightLast ≠
          left.lineGraphJunctionAt leftFirst
    · have hne := penultimate_ne_snd_of_tail_disjoint left right
        hleftTwo (by omega) hdisjoint
      let shortcut := closedBounceShortcut left right hleftTwo
        (by omega) hfirstEq hne
      refine ⟨first, shortcut, ?_, ?_, ?_⟩
      · dsimp only [shortcut]
        have hadd := closedBounceShortcut_length_add_one left right
          hleftTwo (by omega) hfirstEq hne
        rw [SimpleGraph.Walk.length_append] at hadd
        omega
      · dsimp only [shortcut]
        exact closedBounceShortcut_isPrimalCoherentClosed left right
          hleftTwo (by omega) hfirstEq hne hleftCoherent
          hrightCoherent hsecond
      · dsimp only [shortcut]
        have hadd := closedBounceShortcut_length_add_one left right
          hleftTwo (by omega) hfirstEq hne
        omega
    · have hsecondEq := not_ne_iff.mp hsecond
      rcases exists_isPrimalCoherentClosed_of_two_bounces left right
          hleftTwo hrightTwo hleftCoherent hrightCoherent hdisjoint
          hfirstEq hsecondEq with
        ⟨edge, shortcut, hpositive, hcoherent, hlength⟩
      exact ⟨edge, shortcut, hpositive, hcoherent, by omega⟩

end

end SimpleGraph.Walk
